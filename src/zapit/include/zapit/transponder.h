/*
 * Copyright (C) 2012 CoolStream International Ltd
 *
 * License: GPLv2
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation;
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 */

#ifndef _TRANSPONDER_H_
#define _TRANSPONDER_H_

#include <linux/dvb/frontend.h>
#include <zapit/types.h>
#include <string>
#include <map>

class transponder
{
public:
	t_transport_stream_id transport_stream_id;
	t_original_network_id original_network_id;
	transponder_id_t transponder_id;
	t_satellite_position satellitePosition;

	struct dvb_frontend_parameters feparams;
	unsigned char polarization;
	bool updated;
	bool scanned;

	transponder(const transponder_id_t t_id, const struct dvb_frontend_parameters p_feparams, const uint8_t p_polarization = 0);

	bool operator==(const transponder& t) const;
	void dump(std::string label = "tp", bool cable = 0);
};

typedef std::map <transponder_id_t, transponder> transponder_list_t;
typedef std::map <transponder_id_t, transponder>::iterator stiterator;
typedef std::pair<transponder_id_t, transponder> transponder_pair_t;

#endif
