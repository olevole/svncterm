/*
     Copyright (C) 2006 Universitat Politecnica de Valencia
     * Removing the usage of TLS and the need of patched versions of libraries

     Copyright (C) 2007-2011 Proxmox Server Solutions GmbH

     Copyright: vzdump is under GNU GPL, the GNU General Public License.

     This program is free software; you can redistribute it and/or modify
     it under the terms of the GNU General Public License as published by
     the Free Software Foundation; version 2 dated June, 1991.

     This program is distributed in the hope that it will be useful,
     but WITHOUT ANY WARRANTY; without even the implied warranty of
     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
     GNU General Public License for more details.

     You should have received a copy of the GNU General Public License
     along with this program; if not, write to the Free Software
     Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
     02111-1307, USA.

     Author: Dietmar Maurer <dietmar@proxmox.com>

*/

#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h> 
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <rfb/rfb.h>
#include <rfb/keysym.h>
#include <unistd.h>
#include <termios.h>
#include <libutil.h>
#include <string.h>
#include <errno.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <signal.h>
#include <locale.h>

#include <sys/param.h>
#include <sys/jail.h>

#include <jail.h>

#include "vncterm.h"
#include "glyphs.h"

#define	JP_USER		0x01000000
#define	JP_OPT		0x02000000

#define	PRINT_DEFAULT	0x01
#define	PRINT_HEADER	0x02
#define	PRINT_NAMEVAL	0x04
#define	PRINT_QUOTED	0x08
#define	PRINT_SKIP	0x10
#define	PRINT_VERBOSE	0x20
#define	PRINT_JAIL_NAME	0x40

static struct jailparam *params;
static int *param_parent;
static int nparams;

static int add_param(const char *name, void *value, size_t valuelen,
		struct jailparam *source, unsigned flags);
static int print_jail(int pflags, int jflags);

int is_number(const char *p);
int is_numbercmd(int argc, char **argv);
int isnum = 0;
int findjid = -1;
char *findjname = NULL;
char vncpassword[50];
int vncport = 0;
char *listen_str;

#define is_digit(c)	((unsigned int)((c) - '0') <= 9)

/* define this for debugging */
//#define DEBUG

#define DH_BITS 1024
#define TERM "xterm"

#define TERMIDCODE "[?1;2c" // vt100 ID

/* these colours are from linux kernel drivers/char/vt.c */

static int idle_timeout = 1;

unsigned char color_table[] = { 0, 4, 2, 6, 1, 5, 3, 7,
				8,12,10,14, 9,13,11,15 };

/* the default colour table, for VGA+ colour systems */
int default_red[] = {0x00,0xaa,0x00,0xaa,0x00,0xaa,0x00,0xaa,
    0x55,0xff,0x55,0xff,0x55,0xff,0x55,0xff};
int default_grn[] = {0x00,0x00,0xaa,0x55,0x00,0x00,0xaa,0xaa,
    0x55,0x55,0xff,0xff,0x55,0x55,0xff,0xff};
int default_blu[] = {0x00,0x00,0x00,0x00,0xaa,0xaa,0xaa,0xaa,
    0x55,0x55,0x55,0x55,0xff,0xff,0xff,0xff};

/* Convert UCS2 to UTF8 sequence, trailing zero */
static int
ucs2_to_utf8 (unicode c, char *out)
{
  if (c < 0x80) {
    out[0] = c;			//  0*******
    out[1] = 0;
    return 1;
  } else if (c < 0x800) {
    out[0] = 0xc0 | (c >> 6); 	//  110***** 10******
    out[1] = 0x80 | (c & 0x3f);
    out[2] = 0;
    return 2;
  } else {
    out[0] = 0xe0 | (c >> 12); 	//  1110**** 10****** 10******
    out[1] = 0x80 | ((c >> 6) & 0x3f);
    out[2] = 0x80 | (c & 0x3f);
    out[3] = 0;
    return 3;
  }

  return 0;
}

static void
rfb_draw_char (rfbScreenInfoPtr rfbScreen, int x, int y,
	       unsigned short c, rfbPixel col)
{
  if (c > vt_font_size) {
    rfbLog ("undefined font glyph %d\n", c);
    return;
  }

  int i,j;
  unsigned char *data= vt_font_data + c*16;
  unsigned char d=*data;
  int rowstride=rfbScreen->paddedWidthInBytes;
  char *colour=(char*)&col;

  for(j = 0; j < 16; j++) {
    for(i = 0; i < 8; i++) {
      if ((i&7) == 0) {
	d=*data;
	data++;
      }
      if (d&0x80)
	*(rfbScreen->frameBuffer+(y+j)*rowstride+(x+i)) = *colour;
      d<<=1;
    }
  }
}

static void
draw_char_at (vncTerm *vt, int x, int y, unicode ch, TextAttributes attrib)
{
  if (x < 0 || y < 0 || x >= vt->width || y >= vt->height) { return; }

  int rx = x*8;
  int ry = y*16;
  int rxe = x*8+8;
  int rye = y*16+16;

  int fg, bg;

  if (attrib.invers) {
    bg = attrib.fgcol;
    fg = attrib.bgcol;
  } else {
    bg = attrib.bgcol;
    fg = attrib.fgcol;
  }

  int ec = vt_fontmap[ch];

  rfbFillRect (vt->screen, rx, ry, rxe, rye, bg);

  if (attrib.bold) {
    fg += 8;
  }

  // unsuported attributes = (attrib.blink || attrib.unvisible)

  rfb_draw_char (vt->screen, rx, ry, ec, fg);

  if (attrib.uline) {
    rfbDrawLine (vt->screen, rx, ry + 14, rxe, ry + 14, fg);
  }

  rfbMarkRectAsModified (vt->screen, rx, ry, rxe, rye);

}

static void
vncterm_update_xy (vncTerm *vt, int x, int y)
{
  if (x < 0 || y < 0 || x >= vt->width || y >= vt->height) { return; }

  int y1 = (vt->y_base + y) % vt->total_height;
  int y2 = y1 - vt->y_displ;
  if (y2 < 0) {
    y2 += vt->total_height;
  }
  if (y2 < vt->height) {
    TextCell *c = &vt->cells[y1 * vt->width + x];
    draw_char_at (vt, x, y2, c->ch, c->attrib);
  }
}

static void
vncterm_clear_xy (vncTerm *vt, int x, int y)
{
  if (x < 0 || y < 0 || x >= vt->width || y >= vt->height) { return; }

  int y1 = (vt->y_base + y) % vt->total_height;
  int y2 = y1 - vt->y_displ;
  if (y2 < 0) {
    y2 += vt->total_height;
  }
  if (y2 < vt->height) {
    TextCell *c = &vt->cells[y1 * vt->width + x];
    c->ch = ' ';
    c->attrib = vt->default_attrib;
    c->attrib.fgcol = vt->cur_attrib.fgcol;
    c->attrib.bgcol = vt->cur_attrib.bgcol;

    draw_char_at (vt, x, y, c->ch, c->attrib);
  }
}

static void
vncterm_show_cursor (vncTerm *vt, int show)
{
  int x = vt->cx;
  if (x >= vt->width) {
    x = vt->width - 1;
  }

  int y1 = (vt->y_base + vt->cy) % vt->total_height;
  int y = y1 - vt->y_displ;
  if (y < 0) {
    y += vt->total_height;
  }

  if (y < vt->height) {

    TextCell *c = &vt->cells[y1 * vt->width + x];

    if (show) {
      TextAttributes attrib = vt->default_attrib;
      attrib.invers = !(attrib.invers); /* invert fg and bg */
      draw_char_at (vt, x, y, c->ch, attrib);
    } else {
      draw_char_at (vt, x, y, c->ch, c->attrib);
    }
  }
}

static void
vncterm_refresh (vncTerm *vt)
{
  int x, y, y1;

  rfbFillRect (vt->screen, 0, 0, vt->maxx, vt->maxy, vt->default_attrib.bgcol);

  y1 = vt->y_displ;
  for(y = 0; y < vt->height; y++) {
    TextCell *c = vt->cells + y1 * vt->width;
    for(x = 0; x < vt->width; x++) {
      draw_char_at (vt, x, y, c->ch, c->attrib);
      c++;
    }
    if (++y1 == vt->total_height)
      y1 = 0;
  }
  rfbMarkRectAsModified (vt->screen, 0, 0, vt->maxx, vt->maxy);

  vncterm_show_cursor (vt, 1);
}

static void
vncterm_scroll_down (vncTerm *vt, int top, int bottom, int lines)
{
  if ((top + lines) >= bottom) {
    lines = bottom - top -1;
  }

  if (top < 0 || bottom > vt->height || top >= bottom || lines < 1) {
    return;
  }

  int h = lines * 16;
  int y0 = top*16;
  int y1 = y0 + h;
  int y2 = bottom*16;
  int rowstride = vt->screen->paddedWidthInBytes;
  int rows = (bottom - top - lines)*16;

  char *in = vt->screen->frameBuffer+y0*rowstride;
  char *out = vt->screen->frameBuffer+y1*rowstride;
  memmove(out,in, rowstride*rows);

  memset(vt->screen->frameBuffer+y0*rowstride, 0, h*rowstride);
  rfbMarkRectAsModified (vt->screen, 0, y0, vt->screen->width, y2);

  int i;
  for(i = bottom - top - lines - 1; i >= 0; i--) {
    int src = ((vt->y_base + top + i) % vt->total_height)*vt->width;
    int dst = ((vt->y_base + top + lines + i) % vt->total_height)*vt->width;

    memmove(vt->cells + dst, vt->cells + src, vt->width*sizeof (TextCell));
  }

  for (i = 0; i < lines; i++) {
    int j;
    TextCell *c = vt->cells + ((vt->y_base + top + i) % vt->total_height)*vt->width;
    for(j = 0; j < vt->width; j++) {
      c->attrib = vt->default_attrib;
      c->ch = ' ';
      c++;
    }
  }
}

static void
vncterm_scroll_up (vncTerm *vt, int top, int bottom, int lines, int moveattr)
{
  if ((top + lines) >= bottom) {
    lines = bottom - top - 1;
  }

  if (top < 0 || bottom > vt->height || top >= bottom || lines < 1) {
    return;
  }

  int h = lines * 16;
  int y0 = top*16;
  int y1 = (top + lines)*16;
  int y2 = bottom*16;
  int rowstride = vt->screen->paddedWidthInBytes;
  int rows = (bottom - top - lines)*16;

  char *in = vt->screen->frameBuffer+y1*rowstride;
  char *out = vt->screen->frameBuffer+y0*rowstride;
  memmove(out,in, rowstride*rows);

  memset(vt->screen->frameBuffer+(y2-h)*rowstride, 0, h*rowstride);

  rfbMarkRectAsModified (vt->screen, 0, y0, vt->screen->width, y2);

  if (!moveattr) return;

  // move attributes

  int i;
  for(i = 0; i < (bottom - top - lines); i++) {
    int dst = ((vt->y_base + top + i) % vt->total_height)*vt->width;
    int src = ((vt->y_base + top + lines + i) % vt->total_height)*vt->width;

    memmove(vt->cells + dst, vt->cells + src, vt->width*sizeof (TextCell));
  }

  for (i = 1; i <= lines; i++) {
    int j;
    TextCell *c = vt->cells + ((vt->y_base + bottom - i) % vt->total_height)*vt->width;
    for(j = 0; j < vt->width; j++) {
      c->attrib = vt->default_attrib;
      c->ch = ' ';
      c++;
    }
  }
}

static void
vncterm_virtual_scroll (vncTerm *vt, int lines)
{
  if (vt->altbuf || lines == 0) return;

  if (lines < 0) {
    lines = -lines;
    int i = vt->scroll_height;
    if (i > vt->total_height - vt->height)
      i = vt->total_height - vt->height;
    int y1 = vt->y_base - i;
    if (y1 < 0)
      y1 += vt->total_height;
    for(i = 0; i < lines; i++) {
      if (vt->y_displ == y1) break;
      if (--vt->y_displ < 0) {
	vt->y_displ = vt->total_height - 1;
      }
    }
  } else {
    int i;
    for(i = 0; i < lines; i++) {
      if (vt->y_displ == vt->y_base) break;
      if (++vt->y_displ == vt->total_height) {
	vt->y_displ = 0;
      }
    }

  }

  vncterm_refresh (vt);
}
static void
vncterm_respond_esc (vncTerm *vt, const char *esc)
{
  int len = strlen (esc);
  int i;

  if (vt->ibuf_count < (IBUFSIZE - 1 - len)) {
    vt->ibuf[vt->ibuf_count++] = 27;
    for (i = 0; i < len; i++) {
      vt->ibuf[vt->ibuf_count++] = esc[i];
    }
  }
}

static void
vncterm_put_lf (vncTerm *vt)
{
  if (vt->cy + 1 == vt->region_bottom) {

    if (vt->altbuf || vt->region_top != 0 || vt->region_bottom != vt->height) {
      vncterm_scroll_up (vt, vt->region_top, vt->region_bottom, 1, 1);
      return;
    }

    if (vt->y_displ == vt->y_base) {
      vncterm_scroll_up (vt, vt->region_top, vt->region_bottom, 1, 0);
    }

    if (vt->y_displ == vt->y_base) {
      if (++vt->y_displ == vt->total_height) {
	vt->y_displ = 0;
      }
    }

    if (++vt->y_base == vt->total_height) {
      vt->y_base = 0;
    }

    if (vt->scroll_height < vt->total_height) {
      vt->scroll_height++;
    }

    int y1 = (vt->y_base + vt->height - 1) % vt->total_height;
    TextCell *c = &vt->cells[y1 * vt->width];
    int x;
    for (x = 0; x < vt->width; x++) {
      c->ch = ' ';
      c->attrib = vt->default_attrib;
      c++;
    }

    // fprintf (stderr, "BASE: %d DISPLAY %d\n", vt->y_base, vt->y_displ);

  } else if (vt->cy < vt->height - 1) {
    vt->cy += 1;
  }
}


static void
vncterm_csi_m (vncTerm *vt)
{
  int i;

  for (i = 0; i < vt->esc_count; i++) {
    switch (vt->esc_buf[i]) {
    case 0: /* reset all console attributes to default */
      vt->cur_attrib = vt->default_attrib;
      break;
    case 1:
      vt->cur_attrib.bold = 1;
      break;
    case 4:
      vt->cur_attrib.uline = 1;
      break;
    case 5:
      vt->cur_attrib.blink = 1;
      break;
    case 7:
      vt->cur_attrib.invers = 1;
      break;
    case 8:
      vt->cur_attrib.unvisible = 1;
      break;
    case 10:
      vt->cur_enc = LAT1_MAP;
      // fixme: dispaly controls = 0 ?
      // fixme: toggle meta = 0 ?
      break;
    case 11:
      vt->cur_enc = IBMPC_MAP;
      // fixme: dispaly controls = 1 ?
      // fixme: toggle meta = 0 ?
      break;
    case 12:
      vt->cur_enc = IBMPC_MAP;
      // fixme: dispaly controls = 1 ?
      // fixme: toggle meta = 1 ?
      break;
    case 22:
      vt->cur_attrib.bold = 0;
      break;
    case 24:
      vt->cur_attrib.uline = 0;
      break;
    case 25:
      vt->cur_attrib.blink = 0;
      break;
    case 27:
      vt->cur_attrib.invers = 0;
      break;
    case 28:
      vt->cur_attrib.unvisible = 0;
      break;
    case 30:
    case 31:
    case 32:
    case 33:
    case 34:
    case 35:
    case 36:
    case 37:
      /* set foreground color */
      vt->cur_attrib.fgcol = color_table [vt->esc_buf[i] - 30];
      break;
    case 38:
      /* reset color to default, enable underline */
      vt->cur_attrib.fgcol = vt->default_attrib.fgcol;
      vt->cur_attrib.uline = 1;
      break;
    case 39:
      /* reset color to default, disable underline */
      vt->cur_attrib.fgcol = vt->default_attrib.fgcol;
      vt->cur_attrib.uline = 0;
      break;
    case 40:
    case 41:
    case 42:
    case 43:
    case 44:
    case 45:
    case 46:
    case 47:
      /* set background color */
      vt->cur_attrib.bgcol = color_table [vt->esc_buf[i] - 40];
      break;
    case 49:
      /* reset background color */
      vt->cur_attrib.bgcol = vt->default_attrib.bgcol;
      break;
    default:
      fprintf (stderr, "unhandled ESC[%d m code\n",vt->esc_buf[i]);
      //fixme: implement
     }
  }
}

static void
vncterm_save_cursor (vncTerm *vt)
{
  vt->cx_saved = vt->cx;
  vt->cy_saved = vt->cy;
  vt->cur_attrib_saved = vt->cur_attrib;
  vt->charset_saved = vt->charset;
  vt->g0enc_saved = vt->g0enc;
  vt->g1enc_saved = vt->g1enc;
  vt->cur_enc_saved = vt->cur_enc;
}

static void
vncterm_restore_cursor (vncTerm *vt)
{
  vt->cx = vt->cx_saved;
  vt->cy = vt->cy_saved;
  vt->cur_attrib = vt->cur_attrib_saved;
  vt->charset = vt->charset_saved;
  vt->g0enc = vt->g0enc_saved;
  vt->g1enc = vt->g1enc_saved;
  vt->cur_enc = vt->cur_enc_saved;
}

static void
vncterm_set_alternate_buffer (vncTerm *vt, int on_off)
{
  int x, y;

  vt->y_displ = vt->y_base;

  if (on_off) {

    if (vt->altbuf) return;

    vt->altbuf = 1;

    /* alternate buffer & cursor */

    vncterm_save_cursor (vt);
    /* save screen to altcels */
    for (y = 0; y < vt->height; y++) {
      int y1 = (vt->y_base + y) % vt->total_height;
      for (x = 0; x < vt->width; x++) {
	vt->altcells[y*vt->width + x] = vt->cells[y1*vt->width + x];
      }
    }

    /* clear screen */
    for (y = 0; y <= vt->height; y++) {
      for (x = 0; x < vt->width; x++) {
	vncterm_clear_xy (vt, x, y);
      }
    }

  } else {

    if (vt->altbuf == 0) return;

    vt->altbuf = 0;

    /* restore saved data */
    for (y = 0; y < vt->height; y++) {
      int y1 = (vt->y_base + y) % vt->total_height;
      for (x = 0; x < vt->width; x++) {
	vt->cells[y1*vt->width + x] = vt->altcells[y*vt->width + x];
      }
    }

    vncterm_restore_cursor (vt);
  }

  vncterm_refresh (vt);
}

static void
vncterm_set_mode (vncTerm *vt, int on_off)
{
  int i;

  for (i = 0; i <= vt->esc_count; i++) {
    if (vt->esc_ques) {          /* DEC private modes set/reset */
      switch(vt->esc_buf[i]) {
      case 10:                   /* X11 mouse reporting on/off */
      case 1000:
	vt->report_mouse = on_off;
	break;
      case 1049:	 	/* start/end special app mode (smcup/rmcup) */
	vncterm_set_alternate_buffer (vt, on_off);
	break;
      case 25:	 	        /* Cursor on/off */
      case 9:                   /* X10 mouse reporting on/off */
      case 6:			/* Origin relative/absolute */
      case 1:			/* Cursor keys in appl mode*/
      case 5:			/* Inverted screen on/off */
      case 7:			/* Autowrap on/off */
      case 8:			/* Autorepeat on/off */
	break;
      }
    } else { /* ANSI modes set/reset */
      /* fixme: implement me */
    }
  }
}

static void
vncterm_gotoxy (vncTerm *vt, int x, int y)
{
  /* verify all boundaries */

  if (x < 0) {
    x = 0;
  }

  if (x >= vt->width) {
    x = vt->width - 1;
  }

  vt->cx = x;

  if (y < 0) {
    y = 0;
  }

  if (y >= vt->height) {
    y = vt->height - 1;
  }

  vt->cy = y;
}

enum { ESnormal, ESesc, ESsquare, ESgetpars, ESgotpars, ESfunckey,
       EShash, ESsetG0, ESsetG1, ESpercent, ESignore, ESnonstd,
       ESpalette, ESidquery, ESosc1, ESosc2};

static void
vncterm_putchar (vncTerm *vt, unicode ch)
{
  int x, y, i, c;

#ifdef DEBUG
  if (!vt->tty_state)
  fprintf (stderr, "CHAR:%2d: %4x '%c' (cur_enc %d) %d %d\n", vt->tty_state, ch, ch, vt->cur_enc, vt->cx, vt->cy);
#endif

  switch(vt->tty_state) {
  case ESesc:
    vt->tty_state = ESnormal;
    switch (ch) {
    case '[':
      vt->tty_state = ESsquare;
      break;
    case ']':
      vt->tty_state = ESnonstd;
      break;
    case '%':
      vt->tty_state = ESpercent;
      break;
    case '7':
      vncterm_save_cursor (vt);
      break;
    case '8':
      vncterm_restore_cursor (vt);
      break;
    case '(':
      vt->tty_state = ESsetG0; // SET G0
      break;
    case ')':
      vt->tty_state = ESsetG1; // SET G1
      break;
    case 'M':
      /* cursor up (ri) */
      if (vt->cy == vt->region_top)
	vncterm_scroll_down (vt, vt->region_top, vt->region_bottom, 1);
      else if (vt->cy > 0) {
	vt->cy--;
      }
      break;
    case '>':
      /* numeric keypad  - ignored */
      break;
    case '=':
      /* appl. keypad - ignored */
      break;
    default:
#ifdef DEBUG
      fprintf(stderr, "got unhandled ESC%c  %d\n", ch, ch);
#endif
      break;
    }
    break;
  case ESnonstd: /* Operating System Controls */
    vt->tty_state = ESnormal;

    switch (ch) {
    case 'P':   /* palette escape sequence */
      for(i = 0; i < MAX_ESC_PARAMS; i++) {
	vt->esc_buf[i] = 0;
      }

      vt->esc_count = 0;
      vt->tty_state = ESpalette;
      break;
    case 'R':   /* reset palette */
      // fixme: reset_palette(vc);
      break;
    case '0':
    case '1':
    case '2':
    case '4':
      vt->osc_cmd = ch;
      vt->osc_textbuf[0] = 0;
      vt->tty_state = ESosc1;
      break;
    default:
#ifdef DEBUG
      fprintf (stderr, "unhandled OSC %c\n", ch);
#endif
      vt->tty_state = ESnormal;
      break;
    }
    break;
  case ESosc1:
    vt->tty_state = ESnormal;
    if (ch == ';') {
      vt->tty_state = ESosc2;
    } else {
#ifdef DEBUG
      fprintf (stderr, "got illegal OSC sequence\n");
#endif
    }
    break;
  case ESosc2:
    if (ch != 0x9c && ch != 7) {
      int i = 0;
      while (vt->osc_textbuf[i]) i++;
      vt->osc_textbuf[i++] = ch;
      vt->osc_textbuf[i] = 0;
    } else {
#ifdef DEBUG
      fprintf (stderr, "OSC:%c:%s\n", vt->osc_cmd, vt->osc_textbuf);
#endif
      vt->tty_state = ESnormal;
    }
    break;
  case ESpalette:
    if ((ch >= '0' && ch <= '9') || (ch >= 'A' && ch <= 'F')
	|| (ch >= 'a' && ch <= 'f')) {
      vt->esc_buf[vt->esc_count++] = (ch > '9' ? (ch & 0xDF) - 'A' + 10 : ch - '0');
      if (vt->esc_count == 7) {
	// fixme: this does not work - please test
	rfbColourMap *cmap =&vt->screen->colourMap;

	int i = color_table[vt->esc_buf[0]] * 3, j = 1;
	cmap->data.bytes[i] = 16 * vt->esc_buf[j++];
	cmap->data.bytes[i++] += vt->esc_buf[j++];
	cmap->data.bytes[i] = 16 * vt->esc_buf[j++];
	cmap->data.bytes[i++] += vt->esc_buf[j++];
	cmap->data.bytes[i] = 16 * vt->esc_buf[j++];
	cmap->data.bytes[i] += vt->esc_buf[j];

	//set_palette(vc); ?

	vt->tty_state = ESnormal;
      }
    } else
       vt->tty_state = ESnormal;
    break;
  case ESsquare:
    for(i = 0; i < MAX_ESC_PARAMS; i++) {
      vt->esc_buf[i] = 0;
    }

    vt->esc_count = 0;
    vt->esc_has_par = 0;
    vt->tty_state = ESgetpars;

    if (ch == '>') {
      vt->tty_state = ESidquery;
      break;
    }

    if ((vt->esc_ques = (ch == '?'))) {
      break;
    }
  case ESgetpars:
    if (ch >= '0' && ch <= '9') {
      vt->esc_has_par = 1;
      if (vt->esc_count < MAX_ESC_PARAMS) {
	vt->esc_buf[vt->esc_count] = vt->esc_buf[vt->esc_count] * 10 + ch - '0';
      }
      break;
    } else if (ch == ';') {
      vt->esc_count++;
      break;
    } else {
      if (vt->esc_has_par) {
	vt->esc_count++;
      }
      vt->tty_state = ESgotpars;
    }
  case ESgotpars:

    vt->tty_state = ESnormal;

#ifdef DEBUG
    char *qes = vt->esc_ques ? "?" : "";
    if (vt->esc_count == 0) {
      fprintf(stderr, "ESC[%s%c\n", qes, ch);
    } else if (vt->esc_count == 1) {
      fprintf(stderr, "ESC[%s%d%c\n", qes, vt->esc_buf[0], ch);
    } else {
      int i;
      fprintf(stderr, "ESC[%s%d", qes, vt->esc_buf[0]);
      for (i = 1; i < vt->esc_count; i++) {
	fprintf(stderr, ";%d",  vt->esc_buf[i]);
      }
      fprintf (stderr, "%c\n", ch);
    }
#endif

    switch (ch) {
    case 'h':
      vncterm_set_mode (vt, 1);
      break;
    case 'l':
      vncterm_set_mode (vt, 0);
      break;
    case 'm':
      if (!vt->esc_count) {
	vt->esc_count++; // default parameter 0
      }
      vncterm_csi_m (vt);
      break;
    case 'n':
      /* report cursor position */
      /* TODO: send ESC[row;colR */
      break;
    case 'A':
      /* move cursor up */
      if (vt->esc_buf[0] == 0) {
	vt->esc_buf[0] = 1;
      }
      vt->cy -= vt->esc_buf[0];
      if (vt->cy < 0) {
	vt->cy = 0;
      }
      break;
    case 'B':
    case 'e':
      /* move cursor down */
      if (vt->esc_buf[0] == 0) {
	vt->esc_buf[0] = 1;
      }
      vt->cy += vt->esc_buf[0];
      if (vt->cy >= vt->height) {
	vt->cy = vt->height - 1;
      }
      break;
    case 'C':
    case 'a':
      /* move cursor right */
      if (vt->esc_buf[0] == 0) {
	vt->esc_buf[0] = 1;
      }
      vt->cx += vt->esc_buf[0];
      if (vt->cx >= vt->width) {
	vt->cx = vt->width - 1;
      }
      break;
    case 'D':
      /* move cursor left */
      if (vt->esc_buf[0] == 0) {
	vt->esc_buf[0] = 1;
      }
      vt->cx -= vt->esc_buf[0];
      if (vt->cx < 0) {
	vt->cx = 0;
      }
      break;
    case 'G':
    case '`':
      /* move cursor to column */
      vncterm_gotoxy (vt, vt->esc_buf[0] - 1, vt->cy);
      break;
    case 'd':
      /* move cursor to row */
      vncterm_gotoxy (vt, vt->cx , vt->esc_buf[0] - 1);
      break;
    case 'f':
    case 'H':
      /* move cursor to row, column */
      vncterm_gotoxy (vt, vt->esc_buf[1] - 1,  vt->esc_buf[0] - 1);
      break;
    case 'J':
      switch (vt->esc_buf[0]) {
      case 0:
	/* clear to end of screen */
	for (y = vt->cy; y < vt->height; y++) {
	  for (x = 0; x < vt->width; x++) {
	    if (y == vt->cy && x < vt->cx) {
	      continue;
	    }
	    vncterm_clear_xy (vt, x, y);
	  }
	}
	break;
      case 1:
	/* clear from beginning of screen */
	for (y = 0; y <= vt->cy; y++) {
	  for (x = 0; x < vt->width; x++) {
	    if (y == vt->cy && x > vt->cx) {
	      break;
	    }
	    vncterm_clear_xy (vt, x, y);
	  }
	}
	break;
      case 2:
	/* clear entire screen */
	for (y = 0; y <= vt->height; y++) {
	  for (x = 0; x < vt->width; x++) {
	    vncterm_clear_xy (vt, x, y);
	  }
	}
	break;
      }
      break;
    case 'K':
      switch (vt->esc_buf[0]) {
      case 0:
	/* clear to eol */
	for(x = vt->cx; x < vt->width; x++) {
	  vncterm_clear_xy (vt, x, vt->cy);
	}
	break;
      case 1:
	/* clear from beginning of line */
	for (x = 0; x <= vt->cx; x++) {
	  vncterm_clear_xy (vt, x, vt->cy);
	}
	break;
      case 2:
	/* clear entire line */
	for(x = 0; x < vt->width; x++) {
	  vncterm_clear_xy (vt, x, vt->cy);
	}
	break;
      }
      break;
    case 'L':
      /* insert line */
      c = vt->esc_buf[0];

      if (c > vt->height - vt->cy)
	c = vt->height - vt->cy;
      else if (!c)
	c = 1;

      vncterm_scroll_down (vt, vt->cy, vt->region_bottom, c);
      break;
    case 'M':
      /* delete line */
      c = vt->esc_buf[0];

      if (c > vt->height - vt->cy)
	c = vt->height - vt->cy;
      else if (!c)
	c = 1;

      vncterm_scroll_up (vt, vt->cy, vt->region_bottom, c, 1);
      break;
    case 'T':
      /* scroll down */
      c = vt->esc_buf[0];
      if (!c) c = 1;
      vncterm_scroll_down (vt, vt->region_top, vt->region_bottom, c);
      break;
    case 'S':
      /* scroll up */
      c = vt->esc_buf[0];
      if (!c) c = 1;
      vncterm_scroll_up (vt, vt->region_top, vt->region_bottom, c, 1);
      break;
    case 'P':
      /* delete c character */
      c = vt->esc_buf[0];

      if (c > vt->width - vt->cx)
	c = vt->width - vt->cx;
      else if (!c)
	c = 1;

      for (x = vt->cx; x < vt->width - c; x++) {
	int y1 = (vt->y_base + vt->cy) % vt->total_height;
	TextCell *dst = &vt->cells[y1 * vt->width + x];
	TextCell *src = dst + c;
	*dst = *src;
	vncterm_update_xy (vt, x + c, vt->cy);
	src->ch = ' ';
	src->attrib = vt->default_attrib;
	vncterm_update_xy (vt, x, vt->cy);
      }
      break;
    case 's':
      /* save cursor position */
      vncterm_save_cursor (vt);
      break;
    case 'u':
      /* restore cursor position */
      vncterm_restore_cursor (vt);
      break;
    case 'X':
      /* erase c characters */
      c = vt->esc_buf[0];
      if (!c) c = 1;

      if (c > (vt->width - vt->cx)) c = vt->width - vt->cx;

      for(i = 0; i < c; i++) {
	vncterm_clear_xy (vt, vt->cx + i, vt->cy);
      }
      break;
    case '@':
      /* insert c character */
      c = vt->esc_buf[0];
      if (c > (vt->width - vt->cx)) {
	c = vt->width - vt->cx;
      }
      if (!c) c = 1;

      for (x = vt->width - c; x >= vt->cx; x--) {
	int y1 = (vt->y_base + vt->cy) % vt->total_height;
	TextCell *src = &vt->cells[y1 * vt->width + x];
	TextCell *dst = src + c;
	*dst = *src;
	vncterm_update_xy (vt, x + c, vt->cy);
	src->ch = ' ';
	src->attrib = vt->cur_attrib;
	vncterm_update_xy (vt, x, vt->cy);
      }

      break;
    case 'r':
      /* set region */
      if (!vt->esc_buf[0])
	vt->esc_buf[0]++;
      if (!vt->esc_buf[1])
	vt->esc_buf[1] = vt->height;
      /* Minimum allowed region is 2 lines */
      if (vt->esc_buf[0] < vt->esc_buf[1] &&
	  vt->esc_buf[1] <= vt->height) {
	vt->region_top = vt->esc_buf[0] - 1;
	vt->region_bottom = vt->esc_buf[1];
	vt->cx = 0;
	vt->cy = vt->region_top;
#ifdef DEBUG
	fprintf (stderr, "set region %d %d\n", vt->region_top, vt->region_bottom);
#endif
      }

      break;
    default:
#ifdef DEBUG
      if (vt->esc_count == 0) {
	fprintf(stderr, "unhandled escape ESC[%s%c\n", qes, ch);
      } else if (vt->esc_count == 1) {
	fprintf(stderr, "unhandled escape ESC[%s%d%c\n", qes, vt->esc_buf[0], ch);
      } else {
	int i;
	fprintf(stderr, "unhandled escape ESC[%s%d", qes, vt->esc_buf[0]);
	for (i = 1; i < vt->esc_count; i++) {
	  fprintf(stderr, ";%d",  vt->esc_buf[i]);
	}
	fprintf (stderr, "%c\n", ch);
      }
#endif
      break;
    }
    vt->esc_ques = 0;
    break;
  case ESsetG0: // Set G0
    vt->tty_state = ESnormal;

    if (ch == '0')
      vt->g0enc = GRAF_MAP;
    else if (ch == 'B')
      vt->g0enc = LAT1_MAP;
    else if (ch == 'U')
      vt->g0enc = IBMPC_MAP;
    else if (ch == 'K')
      vt->g0enc = USER_MAP;

    if (vt->charset == 0)
      vt->cur_enc = vt->g0enc;

    break;
  case ESsetG1: // Set G1
    vt->tty_state = ESnormal;

    if (ch == '0')
      vt->g1enc = GRAF_MAP;
    else if (ch == 'B')
      vt->g1enc = LAT1_MAP;
    else if (ch == 'U')
      vt->g1enc = IBMPC_MAP;
    else if (ch == 'K')
      vt->g1enc = USER_MAP;

    if (vt->charset == 1)
      vt->cur_enc = vt->g1enc;

    break;
  case ESidquery: // vt100 query id
    vt->tty_state = ESnormal;

    if (ch == 'c') {
#ifdef DEBUG
      fprintf (stderr, "ESC[>c   Query term ID\n");
#endif
      vncterm_respond_esc (vt, TERMIDCODE);
    }
    break;
  case ESpercent:
    vt->tty_state = ESnormal;
    switch (ch) {
    case '@':  /* defined in ISO 2022 */
      vt->utf8 = 0;
      break;
    case 'G':  /* prelim official escape code */
    case '8':  /* retained for compatibility */
      vt->utf8 = 1;
      break;
    }
    break;
  default: // ESnormal
    vt->tty_state = ESnormal;

    switch(ch) {
    case 0:
      break;
    case 7:  /* alert aka. bell */
      rfbSendBell(vt->screen);
      break;
    case 8:  /* backspace */
      if (vt->cx > 0)
	vt->cx--;
      break;
    case 9:  /* tabspace */
      if (vt->cx + (8 - (vt->cx % 8)) > vt->width) {
	vt->cx = 0;
	vncterm_put_lf (vt);
      } else {
	vt->cx = vt->cx + (8 - (vt->cx % 8));
      }
      break;
    case 10:  /* LF,*/
    case 11:  /* VT */
    case 12:  /* FF */
      vncterm_put_lf (vt);
      break;
    case 13:  /* carriage return */
      vt->cx = 0;
      break;
    case 14:
      /* SI (shift in), select character set 1 */
      vt->charset = 1;
      vt->cur_enc = vt->g1enc;
      /* fixme: display controls = 1 */
      break;
    case 15:
      /* SO (shift out), select character set 0 */
      vt->charset = 0;
      vt->cur_enc = vt->g0enc;
      /* fixme: display controls = 0 */
      break;
    case 27:    /* esc */
      vt->tty_state = ESesc;
      break;
    case 127: /* delete */
      /* ignore */
      break;
    case 128+27:    /* csi */
      vt->tty_state = ESsquare;
      break;
    default:
      if (vt->cx >= vt->width) {
	/* line wrap */
	vt->cx = 0;
	vncterm_put_lf (vt);
      }

      int y1 = (vt->y_base + vt->cy) % vt->total_height;
      TextCell *c = &vt->cells[y1*vt->width + vt->cx];
      c->attrib = vt->cur_attrib;
      c->ch = ch;
      vncterm_update_xy (vt, vt->cx, vt->cy);
      vt->cx++;
      break;
    }
    break;
  }
}

static int
vncterm_puts (vncTerm *vt, const char *buf, int len)
{
    unicode tc;

    vncterm_show_cursor (vt, 0);

    while (len) {
      unsigned char c = *buf;
      len--;
      buf++;

      if (vt->tty_state != ESnormal) {
	// never translate escape sequence
	tc = c;
      } else if (vt->utf8 && !vt->cur_enc) {

	if(c & 0x80) { // utf8 multi-byte sequence

	  if (vt->utf_count > 0 && (c & 0xc0) == 0x80) {
	    // inside UTF8 sequence
	    vt->utf_char = (vt->utf_char << 6) | (c & 0x3f);
	    vt->utf_count--;
	    if (vt->utf_count == 0) {
	      tc = vt->utf_char;
	    } else {
	      continue;
	    }
	  } else {
	    //  first char of a UTF8 sequence
	    if ((c & 0xe0) == 0xc0) {
	      vt->utf_count = 1;
	      vt->utf_char = (c & 0x1f);
	    } else if ((c & 0xf0) == 0xe0) {
	      vt->utf_count = 2;
	      vt->utf_char = (c & 0x0f);
	    } else if ((c & 0xf8) == 0xf0) {
	      vt->utf_count = 3;
	      vt->utf_char = (c & 0x07);
	    } else if ((c & 0xfc) == 0xf8) {
	      vt->utf_count = 4;
	      vt->utf_char = (c & 0x03);
	    } else if ((c & 0xfe) == 0xfc) {
	      vt->utf_count = 5;
	      vt->utf_char = (c & 0x01);
	    } else
	      vt->utf_count = 0;

	    continue;
	  }
	} else {
	  // utf8 single byte
	  tc = c;
	  vt->utf_count = 0;
	}

      }	else {
	// never translate controls
	if (c >= 32 && c != 127 && c != (128+27)) {
	  tc = translations[vt->cur_enc][c & 0x0ff];
	} else {
	  tc = c;
	}
      }

      vncterm_putchar (vt, tc);
    }

    vncterm_show_cursor (vt, 1);
    return len;
}

void
vncterm_kbd_event (rfbBool down, rfbKeySym keySym, rfbClientPtr cl)
{
  vncTerm *vt =(vncTerm *)cl->screen->screenData;
  static int control = 0;
  static int shift = 0;
  char *esc = NULL;

  //fprintf (stderr, "KEYEVENT:%d: %08x\n", down == 0, keySym);fflush (stderr);
  if (down) {
    //fprintf (stderr, "KEYPRESS: %d\n", keySym);fflush (stderr);

    if (keySym == XK_Shift_L || keySym == XK_Shift_R) {
      shift = 1;
    } if (keySym == XK_Control_L || keySym == XK_Control_R) {
      control = 1;
    } else if (vt->ibuf_count < (IBUFSIZE - 32)) {

      if (control) {
	if(keySym >= 'a' && keySym <= 'z')
	  keySym -= 'a' -1;
	else if (keySym >= 'A' && keySym <= 'Z')
	  keySym -= 'A'-1;
	else
	  keySym=0xffff;
      } else {
	switch (keySym) {
	case XK_Escape:
	  keySym=27; break;
	case XK_Return:
	  keySym='\r'; break;
	case XK_BackSpace:
	  keySym=8; break;
	case XK_Tab:
	  keySym='\t'; break;
	case XK_Delete: /* kdch1 */
	case XK_KP_Delete:
	  esc = "[3~";break;
	case XK_Home: /* khome */
	case XK_KP_Home:
	  esc = "OH";break;
	case XK_End:
	case XK_KP_End: /* kend */
	  esc = "OF";break;
	case XK_Insert: /* kich1 */
	case XK_KP_Insert:
	  esc = "[2~";break;
	case XK_Up:
	case XK_KP_Up:  /* kcuu1 */
	  esc = "OA";break;
	case XK_Down: /* kcud1 */
	case XK_KP_Down:
	  esc = "OB";break;
	case XK_Right:
	case XK_KP_Right: /* kcuf1 */
	  esc = "OC";break;
	case XK_Left:
	case XK_KP_Left: /* kcub1 */
	  esc = "OD";break;
	case XK_Page_Up:
	  if (shift) {
	    vncterm_virtual_scroll (vt, -vt->height/2);
	    return;
	  }
	  esc = "[5~";break;
	case XK_Page_Down:
	  if (shift) {
	    vncterm_virtual_scroll (vt, vt->height/2);
	    return;
	  }
	  esc = "[6~";break;
	case XK_F1:
	  esc = "OP";break;
	case XK_F2:
	  esc = "OQ";break;
	case XK_F3:
	  esc = "OR";break;
	case XK_F4:
	  esc = "OS";break;
	case XK_F5:
	  esc = "[15~";break;
	case XK_F6:
	  esc = "[17~";break;
	case XK_F7:
	  esc = "[18~";break;
	case XK_F8:
	  esc = "[19~";break;
	case XK_F9:
	  esc = "[20~";break;
	case XK_F10:
	  esc = "[21~";break;
	case XK_F11:
	  esc = "[23~";break;
	case XK_F12:
	  esc = "[24~";break;
	default:
	  break;
	}
      }

#ifdef DEBUG
      fprintf (stderr, "KEYPRESS OUT:%s: %d\n", esc, keySym); fflush (stderr);
#endif

      if (vt->y_displ != vt->y_base) {
	vt->y_displ = vt->y_base;
	vncterm_refresh (vt);
      }

      if (esc) {
	vncterm_respond_esc (vt, esc);
      } else if(keySym<0x100) {
	if (vt->utf8) {
	  int len = ucs2_to_utf8 (keySym & 0x0fff, &vt->ibuf[vt->ibuf_count]);
	  vt->ibuf_count += len;
	} else {
	  vt->ibuf[vt->ibuf_count++] = (char)keySym;
	}
      }
    }
  } else {
    if (keySym == XK_Shift_L || keySym == XK_Shift_R) {
      shift = 0;
    } else if (keySym == XK_Control_L || keySym == XK_Control_R) {
      control = 0;
    }
  }
}

void
vncterm_set_xcut_text (char* str, int len, struct _rfbClientRec* cl)
{
  vncTerm *vt =(vncTerm *)cl->screen->screenData;

  // seems str is Latin-1 encoded
  if (vt->selection) free (vt->selection);
  vt->selection = (unicode *)malloc (len*sizeof (unicode));
  int i;
  for (i = 0; i < len; i++) {
    vt->selection[i] = str[i] & 0xff;
  }
  vt->selection_len = len;
}

static void
mouse_report (vncTerm *vt, int butt, int mrx, int mry)
{
  char buf[8];

  sprintf (buf, "[M%c%c%c", (char)(' ' + butt), (char)('!' + mrx),
	   (char)('!' + mry));

  vncterm_respond_esc (vt, buf);
}

void
vncterm_toggle_marked_cell (vncTerm *vt, int pos)
{
  int x= (pos%vt->width)*8;
  int y= (pos/vt->width)*16;

  int i,j;
  rfbScreenInfoPtr s=vt->screen;

  char *b = s->frameBuffer+y*s->width+x;

  for (j=0; j < 16; j++) {
    for(i=0; i < 8; i++) {
      b[j*s->width+i] ^= 0x0f;
      rfbMarkRectAsModified (s, x, y, x+8, y+16);
    }
  }
}

void
vncterm_pointer_event (int buttonMask, int x, int y, rfbClientPtr cl)
{
  vncTerm *vt =(vncTerm *)cl->screen->screenData;
  static int button2_released = 1;
  static int last_mask = 0;
  static int sel_start_pos = 0;
  static int sel_end_pos = 0;
  int i;

  int cx = x/8;
  int cy = y/16;

  if (cx < 0) cx = 0;
  if (cx >= vt->width) cx = vt->width - 1;
  if (cy < 0) cy = 0;
  if (cy >= vt->height) cy = vt->height - 1;

  if (vt->report_mouse && buttonMask != last_mask) {
    last_mask = buttonMask;
    if (buttonMask & 1) {
      mouse_report (vt, 0, cx, cy);
    }
    if (buttonMask & 2) {
      mouse_report (vt, 1, cx, cy);
    }
    if (buttonMask & 4) {
      mouse_report (vt, 2, cx, cy);
    }
    if (!buttonMask) {
      mouse_report (vt, 3, cx, cy);
    }
  }

  if (buttonMask & 2) {
    if(button2_released && vt->selection) {
      int i;
      for(i = 0; i < vt->selection_len; i++) {
	if (vt->ibuf_count < IBUFSIZE - 6) { // uft8 is max 6 characters wide
	  if (vt->utf8) {
	    vt->ibuf_count += ucs2_to_utf8 (vt->selection[i], &vt->ibuf[vt->ibuf_count]);
	  } else  {
	    vt->ibuf[vt->ibuf_count++] = vt->selection[i];
	  }
	}
      }
      if (vt->y_displ != vt->y_base) {
	vt->y_displ = vt->y_base;
	vncterm_refresh (vt);
      }
    }
    button2_released = 0;
  } else {
    button2_released = 1;
  }

  if (buttonMask & 1) {
    int pos = cy*vt->width + cx;

    // code borrowed from libvncserver (VNConsole.c)

    if (!vt->mark_active) {

      vt->mark_active = 1;
      sel_start_pos = sel_end_pos = pos;
      vncterm_toggle_marked_cell (vt, pos);

    } else {

      if (pos != sel_end_pos) {

	if (pos > sel_end_pos) {
	  cx = sel_end_pos; cy=pos;
	} else {
	  cx=pos; cy=sel_end_pos;
	}

	if (cx < sel_start_pos) {
	  if (cy < sel_start_pos) cy--;
	} else {
	  cx++;
	}

	while (cx <= cy) {
	  vncterm_toggle_marked_cell (vt, cx);
	  cx++;
	}

	sel_end_pos = pos;
      }
    }

  } else if (vt->mark_active) {
    vt->mark_active = 0;

    if (sel_start_pos > sel_end_pos) {
      int tmp = sel_start_pos - 1;
      sel_start_pos = sel_end_pos;
      sel_end_pos = tmp;
    }

    int len = sel_end_pos - sel_start_pos + 1;

    if (vt->selection) free (vt->selection);
    vt->selection = (unicode *)malloc (len*sizeof (unicode));
    vt->selection_len = len;
    char *sel_latin1 = (char *)malloc (len + 1);

    for (i = 0; i < len; i++) {
      int pos = sel_start_pos + i;
      int x = pos % vt->width;
      int y1 = ((pos / vt->width) + vt->y_displ) % vt->total_height;
      TextCell *c = &vt->cells[y1*vt->width + x];
      vt->selection[i] = c->ch;
      sel_latin1[i] = (char)c->ch;
      c++;
    }
    sel_latin1[len] = 0;
    rfbGotXCutText (vt->screen, sel_latin1, len);
    free (sel_latin1);

    while (sel_start_pos <= sel_end_pos) {
      vncterm_toggle_marked_cell (vt, sel_start_pos++);
    }

  }

  rfbDefaultPtrAddEvent (buttonMask, x, y, cl);
}

static int client_count = 0;
static int client_connected = 0;
static int last_client = 1;
static time_t last_time = 0;

void
client_gone (rfbClientPtr client)
{
  client_count--;

  last_time = time (NULL);

  if (client_count <= 0) {
    last_client = 1;
  }
}

/* libvncserver callback for when a new client connects */
enum rfbNewClientAction
new_client (rfbClientPtr client)
{
  client->clientGoneHook = client_gone;
  client_count++;

  last_time = time (NULL);

  last_client = 0;
  client_connected = 1;

  return RFB_CLIENT_ACCEPT;
}

/*
 * Send the authentication challenge.
 */

static void
rfbVncAuthSendChallenge(rfbClientPtr cl)
{
	
    /* 4 byte header is alreay sent. Which is rfbSecTypeVncAuth 
       (same as rfbVncAuth). Just send the challenge. */
    rfbRandomBytes(cl->authChallenge);
    if (rfbWriteExact(cl, (char *)cl->authChallenge, CHALLENGESIZE) < 0) {
        rfbLogPerror("rfbAuthNewClient: write");
        rfbCloseClient(cl);
        return;
    }
    
    /* Dispatch client input to rfbVncAuthProcessResponse. */
    cl->state = RFB_AUTHENTICATION;
}

/*
 * Send the NO AUTHENTICATION. SCARR
 */

static void
rfbVncAuthNone(rfbClientPtr cl)
{
    uint32_t authResult;

    if (cl->protocolMajorVersion==3 && cl->protocolMinorVersion > 7) {
        rfbLog("rfbProcessClientSecurityType: returning securityResult for client rfb version >= 3.8\n");
        authResult = Swap32IfLE(rfbVncAuthOK);
        if (rfbWriteExact(cl, (char *)&authResult, 4) < 0) {
            rfbLogPerror("rfbAuthProcessClientMessage: write");
            rfbCloseClient(cl);
            return;
        }
    }
    cl->state = RFB_INITIALISATION;
    return;
}


/*
 * Advertise the supported security types (protocol 3.7). Here before sending 
 * the list of security types to the client one more security type is added 
 * to the list if primaryType is not set to rfbSecTypeInvalid. This security
 * type is the standard vnc security type which does the vnc authentication
 * or it will be security type for no authentication.
 * Different security types will be added by applications using this library.
 */

static rfbSecurityHandler VncSecurityHandlerVncAuth = {
    rfbSecTypeVncAuth,
    rfbVncAuthSendChallenge,
    NULL
};

static rfbSecurityHandler VncSecurityHandlerNone = {
    rfbSecTypeNone,
    rfbVncAuthNone,
    NULL
};

rfbBool CheckPasswordByList(rfbClientPtr cl,const char* response,int len) {
  char **passwds;
  int i=0;

  for(passwds=(char**)cl->screen->authPasswdData;*passwds;passwds++,i++) {
    uint8_t auth_tmp[CHALLENGESIZE];
    memcpy((char *)auth_tmp, (char *)cl->authChallenge, CHALLENGESIZE);
    rfbEncryptBytes(auth_tmp, *passwds);

    if (memcmp(auth_tmp, response, len) == 0) {
      if(i>=cl->screen->authPasswdFirstViewOnly)
	cl->viewOnly=TRUE;
      return(TRUE);
    }
  }
  // Missed return value and so accepted invalid passwords
  return (FALSE);
}

vncTerm *
create_vncterm (int argc, char** argv, int maxx, int maxy)
{
  int i;
  int ok;

  rfbScreenInfoPtr screen = rfbGetScreen (&argc, argv, maxx, maxy, 8, 1, 1);
  screen->frameBuffer=(char*)calloc(maxx*maxy, 1);

  vncTerm *vt = (vncTerm *)calloc (sizeof(vncTerm), 1);

  rfbColourMap *cmap =&screen->colourMap;
  cmap->data.bytes = malloc (16*3);
  for(i=0;i<16;i++) {
    cmap->data.bytes[i*3 + 0] = default_red[color_table[i]];
    cmap->data.bytes[i*3 + 1] = default_grn[color_table[i]];
    cmap->data.bytes[i*3 + 2] = default_blu[color_table[i]];
  }
  cmap->count = 16;
  cmap->is16 = FALSE;
  screen->serverFormat.trueColour = FALSE;

  screen->kbdAddEvent = vncterm_kbd_event;

  screen->setXCutText = vncterm_set_xcut_text;

  screen->ptrAddEvent = vncterm_pointer_event;

//  screen->desktopName = "VNC Terminal";
  screen->desktopName = findjname;

  screen->newClientHook = new_client;

    if (strlen(vncpassword)>1) {
	static const char* passwords[2]={vncpassword,0};
	screen->authPasswdData=(void*)passwords;
    }

    if ( vncport != 0 ) screen->port = vncport;

    ok = 1;

    if (listen_str != NULL) {
		in_addr_t iface = inet_addr(listen_str);
			screen->listenInterface = iface;
    }

//    static const char* passwords[2]={"secret",0};
//    screen->authPasswdData=(void*)passwords;
//    screen->checkPassword=rfbCheckPasswordByList;

  vt->maxx = screen->width;
  vt->maxy = screen->height;

  vt->width = vt->maxx / 8;
  vt->height = vt->maxy / 16;

  vt->total_height = vt->height * 20;
  vt->scroll_height = 0;
  vt->y_base =  0;
  vt->y_displ =  0;

  vt->region_top = 0;
  vt->region_bottom = vt->height;

  vt->g0enc = LAT1_MAP;
  vt->g1enc = GRAF_MAP;
  vt->cur_enc = vt->g0enc;
  vt->charset = 0;

  /* default text attributes */
  vt->default_attrib.bold = 0;
  vt->default_attrib.uline = 0;
  vt->default_attrib.blink = 0;
  vt->default_attrib.invers = 0;
  vt->default_attrib.unvisible = 0;
  vt->default_attrib.fgcol = 7;
  vt->default_attrib.bgcol = 0;

  vt->cur_attrib = vt->default_attrib;

  vt->cells = (TextCell *)calloc (sizeof (TextCell), vt->width*vt->total_height);

  for (i = 0; i < vt->width*vt->total_height; i++) {
    vt->cells[i].ch = ' ';
    vt->cells[i].attrib = vt->default_attrib;
  }

  vt->altcells = (TextCell *)calloc (sizeof (TextCell), vt->width*vt->height);

  vt->screen = screen;

  screen->screenData = (void*)vt;

  //screen->autoPort = 1;

  rfbInitServer(screen);
 
  if (screen->authPasswdData && strcmp(((char**)screen->authPasswdData)[0], "")) {
        screen->passwordCheck = CheckPasswordByList;
  	rfbRegisterSecurityHandler(&VncSecurityHandlerVncAuth);
  }
  else {
	screen->authPasswdData = NULL;
        screen->passwordCheck = NULL;
        rfbRegisterSecurityHandler(&VncSecurityHandlerNone);
  }

  return vt;
}

int
main (int argc, char** argv)
{
	int pid;
	int master;
	int c;
	char ptyname[1024];
	fd_set fs, fs1;
	struct timeval tv, tv1;
	time_t elapsed, cur_time;
	struct winsize dimensions;
	char *ep;
	char *command = NULL;

	int pflags =0;
	int jflags = 0;
	int lastjid = 0;

	memset(vncpassword,0,sizeof(vncpassword));

	while ((c = getopt(argc, argv, "a:j:p:s:t:w:")) >= 0)
		switch (c) {
			case 'a':
				listen_str = malloc(strlen(optarg) + 1);
				memset(listen_str, 0, strlen(optarg) + 1);
				strcpy(listen_str, optarg);
				break;
			case 'j':
				findjid = strtoul(optarg, &ep, 10);
				if (!findjid || *ep) {
					findjid = 0;
					findjname = optarg;
					isnum = 0;
				} else {
					isnum = 1;
				}
				break;
			case 'p':
				vncport = atoi(optarg);
				break;
			case 's':
				command = malloc(strlen(optarg) + 1);
				memset(command, 0, strlen(optarg) + 1);
				strcpy(command, optarg);
				break;
			case 'w':
				strcpy(vncpassword,optarg);
				break;
		}

	if ((findjid==-1)&&(!findjname)) {
		printf("usage: svncterm -j [ jid or jname] [-a listen addr ] [-p port ] [-s command/shell (/bin/csh)] [-t connect timeout] [-w password]\n");
		return 1;
	}

	if ( command == NULL ) command="/bin/csh";

	/* Add the parameters to print. */
	add_param("jid", NULL, (size_t)0, NULL, JP_USER);
	add_param("name", NULL, (size_t)0, NULL, JP_USER);
	add_param("lastjid", &lastjid, sizeof(lastjid), NULL, 0);

	for (lastjid = 0; (lastjid = print_jail(pflags, jflags)) >= 0; ) {
	}

	if (isnum==1) {
		if (!findjname) {
			printf("Can't find jail\n");
			exit(1);
		}
	} else {
		if (findjid < 1) {
			printf("Can't find jail\n");
			exit(1);
		}
	}

	char jid[10];
	memset(jid,0,sizeof(jid));
	sprintf(jid,"%d",findjid);

#ifdef DEBUG
  rfbLogEnable (1);
#else
  rfbLogEnable (0);
#endif

  vncTerm *vt = create_vncterm (argc, argv, 745, 400);

  setlocale(LC_ALL, ""); // set from environment

  char *ctype = setlocale (LC_CTYPE, NULL); // query LC_CTYPE

  // fixme: ist there a standard way to detect utf8 mode ?
  if (strcasestr (ctype, ".utf-8")||strcasestr (ctype, ".utf8")) {
    vt->utf8 = 1;
  }

  dimensions.ws_col = vt->width;
  dimensions.ws_row = vt->height;

  setenv ("TERM", TERM, 1);

  pid = forkpty (&master, ptyname, NULL, &dimensions);
  if(!pid) {

    // install default signal handlers
    signal (SIGQUIT, SIG_DFL);
    signal (SIGTERM, SIG_DFL);
    signal (SIGINT, SIG_DFL);

    execlp("/usr/sbin/jexec", "/usr/sbin/jexec", jid, command, (char *)NULL);
    perror ("Error: exec failed\n");
    exit (-1); // should not be reached
  } else if (pid == -1) {
    perror ("Error: fork failed\n");
    exit (-1);
  }

  FD_ZERO (&fs);
  FD_SET (master, &fs);
  tv.tv_sec = 0;
  tv.tv_usec = 5000; /* 5 ms */

  last_time = time (NULL);

  int count = 0;
  while (1) {
    count ++;
    tv1 = tv;
    fs1 = fs;

    cur_time = time (NULL);

    elapsed = cur_time - last_time;
    //printf ("Elapsed %ld\n", elapsed);

    if (last_client) {
      if (client_connected) {
	if (idle_timeout && (elapsed >= idle_timeout)) {
	  break;
	}
      } else {
	// wait at least 20 seconds for initial connect
//	if (idle_timeout && (elapsed >= (idle_timeout > 20 ? idle_timeout : 20))) {
//	  break;
//	}
      }
    } else {
      // exit after 30 minutes idle time
      if (elapsed >= 30*60) {
	break;
      }
    }

    rfbProcessEvents (vt->screen, 40000); /* 40 ms */

    if (vt->ibuf_count > 0) {
      //printf ("DEBUG: WRITE %d %d\n", vt->ibuf[0], vt->ibuf_count);
      write (master, vt->ibuf, vt->ibuf_count);
      vt->ibuf_count = 0;
      last_time = time (NULL);
    }

    if (!vt->mark_active) {

      int num_fds = select (master+1, &fs1, NULL, NULL, &tv1);
      if (num_fds >= 0) {
	if (FD_ISSET (master, &fs1)) {
	  char buffer[1024];
	  int c;
	  while ((c = read (master, buffer, 1024)) == -1) {
	    if (errno != EAGAIN) break;
	  }
	  if (c == -1) break;
	  vncterm_puts (vt, buffer, c);
	}
      } else {
	break;
      }
    }
  }

  kill (pid, 9);
  int status;
  waitpid(pid, &status, 0);

  exit (0);
}


static int
add_param(const char *name, void *value, size_t valuelen,
	struct jailparam *source, unsigned flags)
{
	struct jailparam *param, *tparams;
	int i, tnparams;

	static int paramlistsize;

	/* The pseudo-parameter "all" scans the list of available parameters. */
	if (!strcmp(name, "all")) {
		tnparams = jailparam_all(&tparams);
		if (tnparams < 0) {
			printf("error: %s", jail_errmsg);
			return 1;
			}
		for (i = 0; i < tnparams; i++)
			add_param(tparams[i].jp_name, NULL, (size_t)0,
			    tparams + i, flags);
		free(tparams);
		return -1;
	}

	/* Check for repeat parameters. */
	for (i = 0; i < nparams; i++)
		if (!strcmp(name, params[i].jp_name)) {
			if (value != NULL && jailparam_import_raw(params + i,
			    value, valuelen) < 0) {
				printf("error: %s", jail_errmsg);
				return 1;
				}
			params[i].jp_flags |= flags;
			if (source != NULL)
				jailparam_free(source, 1);
			return i;
		}

	/* Make sure there is room for the new param record. */
	if (!nparams) {
		paramlistsize = 32;
		params = malloc(paramlistsize * sizeof(*params));
		param_parent = malloc(paramlistsize * sizeof(*param_parent));
		if (params == NULL || param_parent == NULL) {
			printf("malloc");
			return 1;
			}
	} else if (nparams >= paramlistsize) {
		paramlistsize *= 2;
		params = realloc(params, paramlistsize * sizeof(*params));
		param_parent = realloc(param_parent,
		    paramlistsize * sizeof(*param_parent));
		if (params == NULL || param_parent == NULL) {
			printf("realloc");
			return 1;
			}
	}

	/* Look up the parameter. */
	param_parent[nparams] = -1;
	param = params + nparams++;
	if (source != NULL) {
		*param = *source;
		param->jp_flags |= flags;
		return param - params;
	}
	if (jailparam_init(param, name) < 0 ||
		(value != NULL ? jailparam_import_raw(param, value, valuelen)
		: jailparam_import(param, value)) < 0) {
		if (flags & JP_OPT) {
			nparams--;
			return (-1);
		}
		printf("error: %s", jail_errmsg);
		return 1;
	}
	param->jp_flags = flags;
	return param - params;
}

static int
print_jail(int pflags, int jflags)
{
	int jid = 0;

	jid = jailparam_get(params, nparams, jflags);

	if (isnum==1) {
		if (*(int *) params[0].jp_value == findjid ) {
			findjname=(char *)params[1].jp_value;
			jid=-1;
		}
	} else {
		if (!strcmp((char *)params[1].jp_value,findjname)) {
			findjid=*(int *)params[0].jp_value;
			jid=-1;
		}
	}

	return (jid);
}

int is_numbercmd(int argc, char **argv)
{
	if (argv[1])
		return is_number(argv[1]);
	else
		return 1;
}


int is_number(const char *p)
{
	const char *q;

	if (*p == '\0')
		return 0;
	while (*p == '0')
		p++;
	for (q = p; *q != '\0'; q++)
		if (! is_digit(*q))
			return 0;
	if (q - p > 10000 ) return 0;
	return 1;
}
