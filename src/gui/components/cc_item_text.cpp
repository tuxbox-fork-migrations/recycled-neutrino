/*
	Based up Neutrino-GUI - Tuxbox-Project 
	Copyright (C) 2001 by Steffen Hehn 'McClean'

	Classes for generic GUI-related components.
	Copyright (C) 2012, 2013, Thilo Graf 'dbt'
	Copyright (C) 2012, Michael Liebmann 'micha-bbg'

	License: GPL

	This library is free software; you can redistribute it and/or
	modify it under the terms of the GNU Library General Public
	License as published by the Free Software Foundation; either
	version 2 of the License, or (at your option) any later version.

	This library is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
	Library General Public License for more details.

	You should have received a copy of the GNU Library General Public
	License along with this library; if not, write to the
	Free Software Foundation, Inc., 51 Franklin St, Fifth Floor,
	Boston, MA  02110-1301, USA.
*/

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <global.h>
#include <neutrino.h>
#include "cc.h"

using namespace std;

//sub class CComponentsText from CComponentsItem
CComponentsText::CComponentsText()
{
	//CComponentsText
	initVarText();
}

CComponentsText::CComponentsText(	const int x_pos, const int y_pos, const int w, const int h,
					const char* text, const int mode, Font* font_text,
					bool has_shadow,
					fb_pixel_t color_text, fb_pixel_t color_frame, fb_pixel_t color_body, fb_pixel_t color_shadow)
{
	//CComponentsText
	initVarText();

	//CComponents
	x 		= x_pos,
	y 		= y_pos,
	width		= w;
	height		= h;
	
	col_frame	= color_frame;
	col_body	= color_body;
	col_shadow	= color_shadow;
	shadow		= has_shadow;
	
	ct_font 	= font_text;
	ct_text 	= text;
	ct_text_mode	= mode;
	ct_col_text	= color_text;
}



CComponentsText::~CComponentsText()
{
	hide();
	clearSavedScreen();
	clearCCText();
	clear();
}


void CComponentsText::initVarText()
{
	//CComponents, CComponentsItem
	initVarItem();
	cc_item_type 	= CC_ITEMTYPE_TEXT;

	//CComponentsText
	ct_font 	= NULL;
	ct_box		= NULL;
	ct_textbox	= NULL;
	ct_text 	= NULL;
	ct_text_mode	= CTextBox::AUTO_WIDTH;
	ct_col_text	= COL_MENUCONTENT;
	ct_text_sent	= false;
}


void CComponentsText::initCCText()
{
	//set default font, if is no font definied
	if (ct_font == NULL)
		ct_font = g_Font[SNeutrinoSettings::FONT_TYPE_INFOBAR_SMALL];

	//define height from font size
	height 	= max(height, 	ct_font->getHeight());

	//text box dimensions
	if (ct_box== NULL){
		//ensure that we have a new instance
		delete ct_box;
		ct_box = NULL;
	}
	ct_box = new CBox();
	ct_box->iX 	= x+fr_thickness;
	ct_box->iY 	= y+fr_thickness;
	ct_box->iWidth 	= width-2*fr_thickness;
	ct_box->iHeight = height-2*fr_thickness;

	//init textbox
	if (ct_textbox == NULL)
		ct_textbox = new CTextBox();

	//set text box properties
	ct_textbox->setTextFont(ct_font);
	ct_textbox->setTextMode(ct_text_mode);
	ct_textbox->setWindowPos(ct_box);
	ct_textbox->setTextBorderWidth(0);
	ct_textbox->enableBackgroundPaint(false);
	ct_textbox->setBackGroundColor(col_body);
	ct_textbox->setBackGroundRadius(corner_rad-fr_thickness, corner_type);
	ct_textbox->setTextColor(ct_col_text);
	ct_textbox->setWindowMaxDimensions(ct_box->iWidth, ct_box->iHeight);
	ct_textbox->setWindowMinDimensions(ct_box->iWidth, ct_box->iHeight);

	//set text
	string new_text = static_cast <string> (ct_text);
	ct_text_sent = ct_textbox->setText(&new_text, ct_box->iWidth);
#ifdef DEBUG_CC
	printf("    [CComponentsText]   [%s - %d] init text: %s [x %d, y %d, h %d, w %d]\n", __FUNCTION__, __LINE__, ct_text, ct_box->iX, ct_box->iY, height, width);
#endif
}

void CComponentsText::clearCCText()
{
	if (ct_box)
		delete ct_box;
	ct_box = NULL;

	if (ct_textbox)
		delete ct_textbox;
	ct_textbox = NULL;
}

void CComponentsText::setText(neutrino_locale_t locale_text, int mode, Font* font_text)
{
	ct_text = g_Locale->getText(locale_text);
	ct_text_mode = mode;
	ct_font = font_text;

}

void CComponentsText::setText(const char* ctext, const int mode, Font* font_text)
{
	ct_text = ctext;
	ct_text_mode = mode;
	ct_font = font_text;

}

void CComponentsText::setText(const std::string& stext, const int mode, Font* font_text)
{
	ct_text = stext.c_str();
	ct_text_mode = mode;
	ct_font = font_text;
	
}

void CComponentsText::paintText(bool do_save_bg)
{
	paintInit(do_save_bg);
	initCCText();
	if (ct_text_sent)
		ct_textbox->paint();
	ct_text_sent = false;
}

void CComponentsText::paint(bool do_save_bg)
{
	paintText(do_save_bg);
}

void CComponentsText::hide(bool no_restore)
{

	if (ct_textbox)
		ct_textbox->hide();
	hideCCItem(no_restore);
}

//small helper to remove excessiv linbreaks
void CComponentsText::removeLineBreaks(std::string& str)
{
	std::string::size_type spos = str.find_first_of("\r\n");
	while (spos != std::string::npos) {
		str.replace(spos, 1, " ");
		spos = str.find_first_of("\r\n");
	}
}
