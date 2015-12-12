#!/usr/bin/env python
# -*- coding: utf-8 -*-

# kb_builder builts keyboard plate and case CAD files using JSON input.
#
# Copyright (C) 2015  Will Stevens (swill)
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
import json
import logging

import math
import os
import sys

from config import config as cfg

log = logging.getLogger()

if 'lib' in cfg and 'freecad_lib_dir' in cfg['lib'] and cfg['lib']['freecad_lib_dir'] != "":
    sys.path.append(cfg['lib']['freecad_lib_dir'])
if 'lib' in cfg and 'freecad_mod_dir' in cfg['lib'] and cfg['lib']['freecad_mod_dir'] != "":
    for mod in os.listdir(cfg['lib']['freecad_mod_dir']):
        mod_path = os.path.join(cfg['lib']['freecad_mod_dir'], mod)
        if os.path.isdir(mod_path): sys.path.append(mod_path)

import FreeCAD
import cadquery
import importDXF
import importSVG
import Mesh
import Part

SWITCH_LAYER = 'switch'
REINFORCING_LAYER = 'reinforcing'
TOP_LAYER = 'top'
BOTTOM_LAYER = 'bottom'
CLOSED_LAYER = 'closed'
OPEN_LAYER = 'open'

class Plate(object):
    def __init__(self, keyboard_layout, kerf=0.0, case_type=None, corner_type=0, width_padding=0, height_padding=0,
                 usb_width=10, export_svg=False, stab_type=0, corners=0, switch_type=1, usb_offset=0,
                 pcb_height_padding=0, pcb_width_padding=0, mount_holes_num=0, mount_holes_size=0,
                 thickness=1.5, holes=None, reinforcing=False):
        # User settable things
        self.case = {'type': case_type}
        self.corner_type = corner_type
        self.corners = corners
        self.kerf = kerf / 2
        self.keyboard_layout = keyboard_layout
        self.holes = holes if holes else []
        self.stab_type = stab_type
        self.switch_type = switch_type
        self.thickness = thickness
        self.usb_width = usb_width
        self.usb_offset = usb_offset
        self.x_pad = width_padding
        self.x_pcb_pad = pcb_width_padding / 2
        self.y_pad = height_padding
        self.y_pcb_pad = pcb_height_padding / 2

        # Sanity checks
        if not 0 <= switch_type <= 4:
            log.error('Unknown switch type %s, defaulting to 0!', switch_type)
            self.switch_type = 0

        if not 0 <= stab_type <= 4:
            log.error('Unknown stabilizer type %s, defaulting to 0!', stab_type)
            self.stab_type = 0

        # Plate state info
        self.UOM = "mm"
        self.exports = {}
        self.formats = cfg['app']['formats'][:]  # Use a copy in case we remove SVG later
        self.grow_y = 0
        self.grow_x = 0
        self.height = 0
        self.layers = [SWITCH_LAYER]
        self.layout = []
        self.origin = (0,0)
        self.width = 0
        self.x_off = 0

        # Constants
        self.u1 = 19.05
        self.stabs = {
            "300":  (19.05, 0),       # 3 unit
            "400":  (28.575, 0),      # 4 unit
            "450":  (34.671, 0),      # 4.5 unit
            "550":  (42.8625, 0),     # 5.5 unit
            "600":  (47.625, 9.525),  # 6 unit
            "625":  (50, 0),          # 6.25 unit
            "650":  (52.38, 0),       # 6.5 unit
            "700":  (57.15, 0),       # 7 unit
            "800":  (66.675, 0),      # 8 unit
            "900":  (66.675, 0),      # 9 unit
            "1000": (66.675, 0)       # 10 unit
        }

        # Initialize the case
        if self.case['type'] == 'poker':
            if mount_holes_size > 0:
                self.case = {'type': 'poker', 'hole_diameter': mount_holes_size}
        elif self.case['type'] == 'sandwich':
            self.layers += [TOP_LAYER, REINFORCING_LAYER, OPEN_LAYER, CLOSED_LAYER, BOTTOM_LAYER]
            if mount_holes_num > 0 and mount_holes_size > 0:
                self.case = {'type': 'sandwich', 'holes': mount_holes_num, 'hole_diameter': mount_holes_size, 'x_holes':0, 'y_holes':0}
        elif self.case['type']:
            log.error('Unknown case type: %s, skipping case generation', self.case['type'])

        if reinforcing:
            self.layers += [REINFORCING_LAYER]

        # If we don't want SVG remove it from the available formats
        if not export_svg:
            self.formats.remove('svg')

    # this is the main draw function for the class and handles the logical flow and orchestration
    def draw(self, result, data_hash, config):
        self.parse_layout()
        p = self.init_plate()
        result['width'] = self.width
        result['height'] = self.height

        # Cut the beveled corners if applicable
        if self.corners > 0 and self.corner_type == 0:
            pass  # Rounded corners are handled in self.init_plate()
        elif self.corners > 0 and self.corner_type == 1:
            # Lower right corner
            points = (
                (self.horizontal_edge, self.vertical_edge - self.corners), (self.horizontal_edge, self.vertical_edge),
                (self.horizontal_edge - self.corners, self.vertical_edge), (self.horizontal_edge, self.vertical_edge - self.corners),
            )
            p = p.polyline(points).cutThruAll()
            # Lower left corner
            points = (
                (-self.horizontal_edge, self.vertical_edge - self.corners), (-self.horizontal_edge, self.vertical_edge),
                (-self.horizontal_edge + self.corners, self.vertical_edge), (-self.horizontal_edge, self.vertical_edge - self.corners),
            )
            p = p.polyline(points).cutThruAll()
            # Upper right corner
            points = (
                (self.horizontal_edge, -self.vertical_edge + self.corners), (self.horizontal_edge, -self.vertical_edge),
                (self.horizontal_edge - self.corners, -self.vertical_edge), (self.horizontal_edge, -self.vertical_edge + self.corners),
            )
            p = p.polyline(points).cutThruAll()
            # Upper left corner
            points = (
                (-self.horizontal_edge, -self.vertical_edge + self.corners), (-self.horizontal_edge, -self.vertical_edge),
                (-self.horizontal_edge + self.corners, -self.vertical_edge), (-self.horizontal_edge, -self.vertical_edge + self.corners),
            )
            p = p.polyline(points).cutThruAll()
        else:
            log.error('Unknown corner type %s! Disabling corners.', self.corner_type)

        # cut any specified holes
        for hole in self.holes:
            x, y, diameter = hole
            p = p.center(x, y).circle(diameter/2).cutThruAll()
            p = p.center(-x, -y)

        # cut the mount holes in the plate
        if self.case['type'] == 'poker':
            hole_points = [(-139,9.2), (-117.3,-19.4), (-14.3,0), (48,37.9), (117.55,-19.4), (139,9.2)] # holes
            rect_center = (self.width/2) - (3.5/2)
            rect_points = [(rect_center,9.2), (-rect_center,9.2)] # edge slots
            rect_size = (3.5, 5) # edge slot cutout to edge
            for c in hole_points:
                p = p.center(c[0], c[1]).hole(self.case['hole_diameter']).center(-c[0],-c[1])
            for c in rect_points:
                p = p.center(c[0], c[1]).rect(rect_size[0], rect_size[1]).center(-c[0],-c[1])
            p = self.center(p, -self.width/2 + self.kerf, -self.height/2 + self.kerf) # move to top left of the plate
        elif self.case['type'] == 'sandwich':
            p = self.center(p, -self.width/2 + self.kerf, -self.height/2 + self.kerf) # move to top left of the plate
            if 'holes' in self.case and self.case['holes'] >= 4 and 'x_holes' in self.case and 'y_holes' in self.case:
                self.layout_sandwich_holes()
                radius = self.case['hole_diameter']/2 - self.kerf
                x_gap = (self.width - 2*self.case['hole_diameter'] - 2*self.kerf + 1)/(self.case['x_holes'] + 1)
                y_gap = (self.height - 2*self.case['hole_diameter'] - 2*self.kerf + 1)/(self.case['y_holes'] + 1)
                p = p.center(self.case['hole_diameter']-.5, self.case['hole_diameter']-.5)
                for i in range(self.case['x_holes'] + 1):
                    p = p.center(x_gap,0).circle(radius).cutThruAll()
                for i in range(self.case['y_holes'] + 1):
                    p = p.center(0,y_gap).circle(radius).cutThruAll()
                for i in range(self.case['x_holes'] + 1):
                    p = p.center(-x_gap,0).circle(radius).cutThruAll()
                for i in range(self.case['y_holes'] + 1):
                    p = p.center(0,-y_gap).circle(radius).cutThruAll()  # FIXME: Figure out why this one needs p =
                if result['has_layers']:
                    self.export(p, result, BOTTOM_LAYER, data_hash, config)
                p = p.center(-self.case['hole_diameter']+.5, -self.case['hole_diameter']+.5)
        elif not self.case['type'] or self.case['type'] == 'reinforcing':
            p = self.center(p, -self.width/2 + self.kerf, -self.height/2 + self.kerf) # move to top left of the plate
        else:
            log.error('Unknown case type: %s', self.case['type'])

        # cut all the switch and stabilizer openings...
        for layer in (SWITCH_LAYER, REINFORCING_LAYER, TOP_LAYER):
            if layer not in self.layers:
                break

            prev_width = None
            prev_y_off = 0

            if layer != SWITCH_LAYER:
                p = self.center(p, -self.origin[0], -self.origin[1]) # move to the center of the plate
                p = self.center(p, -self.width/2 + self.kerf, -self.height/2 + self.kerf) # move to top left of the plate

            for r, row in enumerate(self.layout):
                for k, key in enumerate(row):
                    x, y, kx = 0, 0, 0
                    if 'x' in key:
                        x = key['x']*self.u1
                        kx = x

                    if 'y' in key and k == 0:
                        y = key['y']*self.u1

                    if r == 0 and k == 0: # handle placement of the first key in first row
                        p = self.center(p, key['w'] * self.u1 / 2, self.u1 / 2)
                        x += (self.x_pad+self.x_pcb_pad)
                        y += (self.y_pad+self.y_pcb_pad)
                        # set x_off negative since the 'cut_switch' will append 'x' and we need to account inital spacing
                        self.x_off = -(x - (self.u1/2 + key['w']*self.u1/2) - kx)
                    elif k == 0: # handle changing rows
                        p = self.center(p, -self.x_off, self.u1) # move to the next row
                        self.x_off = 0 # reset back to the left side of the plate
                        x += self.u1/2 + key['w']*self.u1/2
                    else: # handle all other keys
                        x += prev_width*self.u1/2 + key['w']*self.u1/2

                    if prev_y_off != 0: # prev_y_off != 0
                        y += -prev_y_off
                        prev_y_off = 0

                    if 'h' in key and key['h'] > 1: # deal with vertical keys
                        prev_y_off = key['h']*self.u1/2 - self.u1/2
                        y += prev_y_off

                    else:
                        p = self.cut_switch(p, (x, y), key, layer)

                    prev_width = key['w']

            self.export(p, result, layer, data_hash, config)

        # cut layers
        if CLOSED_LAYER in self.layers:
            p = p.center(-self.origin[0], -self.origin[1])  # move to the center of the plate
            points = [
                (-self.width/2+self.x_pad+self.kerf*2,-self.height/2+self.y_pad+self.kerf*2), (self.width/2-self.x_pad-self.kerf*2,-self.height/2+self.y_pad+self.kerf*2),
                (self.width/2-self.x_pad-self.kerf*2,self.height/2-self.y_pad-self.kerf*2), (-self.width/2+self.x_pad+self.kerf*2,self.height/2-self.y_pad-self.kerf*2),
                (-self.width/2+self.x_pad+self.kerf*2,-self.height/2+self.y_pad+self.kerf*2)
            ]
            p = p.polyline(points).cutThruAll()
            self.export(p, result, CLOSED_LAYER, data_hash, config)

        if OPEN_LAYER in self.layers:
            p = p.center(0, -self.height/2+(self.y_pad+self.y_pcb_pad)/2+self.kerf)

            points = [
                (-self.usb_width/2+self.usb_offset+self.kerf,-(self.y_pad+self.y_pcb_pad)/2-self.kerf), (self.usb_width/2+self.usb_offset-self.kerf,-(self.y_pad+self.y_pcb_pad)/2-self.kerf),
                (self.usb_width/2+self.usb_offset-self.kerf,(self.y_pad+self.y_pcb_pad)/2+self.kerf), (-self.usb_width/2+self.usb_offset+self.kerf,(self.y_pad+self.y_pcb_pad)/2+self.kerf),
                (-self.usb_width/2+self.usb_offset+self.kerf,-(self.y_pad+self.y_pcb_pad)/2-self.kerf)
            ]
            p = p.polyline(points).cutThruAll()
            self.export(p, result, OPEN_LAYER, data_hash, config)
        return result


    # parse the supplied layout to determine size and populate the properties of each 'key'
    def parse_layout(self):
        layout_width = 0
        layout_height = 0
        key_desc = False # track if current is not a key and only describes the next key
        for row in self.keyboard_layout:
            if isinstance(row, list): # only handle arrays of keys
                row_width = 0
                row_height = 0
                row_layout = []
                for k in row:
                    key = {}
                    if isinstance(k, dict): # descibes the next key
                        key = k
                        if 'w' not in key:
                            key['w'] = 1
                        if 'h' not in key:
                            key['h'] = 1
                        row_layout.append(key)
                        key_desc = True
                    else: # is just a standard key (we know its a single unit key)
                        if not key_desc: # only handle if it was not already handled as a key_desc
                            key['w'] = 1
                            key['h'] = 1
                            row_layout.append(key)
                        key_desc = False
                    if 'w' in key:
                        row_width += key['w']
                    if 'x' in key:
                        row_width += key['x'] # offsets count towards total row width
                    if 'y' in key:
                        row_height = key['y']
                self.layout.append(row_layout)
                if row_width > layout_width:
                    layout_width = row_width
                layout_height += self.u1 + row_height*self.u1;
            # hidden global features
            if isinstance(row, dict):
                if 'grow_y' in row and (type(row['grow_y']) == int or type(row['grow_y']) == float):
                    self.grow_y = row['grow_y']/2
                if 'grow_x' in row and (type(row['grow_x']) == int or type(row['grow_x']) == float):
                    self.grow_x = row['grow_x']/2
        self.width = layout_width*self.u1 + 2*(self.x_pad+self.x_pcb_pad) + 2*self.kerf
        self.height = layout_height + 2*(self.y_pad+self.y_pcb_pad) + 2*self.kerf
        self.horizontal_edge = self.width / 2
        self.vertical_edge = self.height / 2


    # initialize the plate object 'p' and get it ready to work with
    def init_plate(self):
        p = cadquery.Workplane("front").box(self.width, self.height, self.thickness)

        if self.corners > 0 and self.corner_type == 0:
            p = p.edges("|Z").fillet(self.corners)

        return p.faces("<Z").workplane()


    # since the sandwich plate has a dynamic number of holes, determine where the specified holes should be placed
    def layout_sandwich_holes(self):
        if 'holes' in self.case and self.case['holes'] >= 4 and 'x_holes' in self.case and 'y_holes' in self.case:
            holes = int(self.case['holes'])
            if holes % 2 == 0 and holes >= 4: # holes needs to be even and the first 4 are put in the corners
                x = self.width - self.kerf # x length to split
                y = self.height - self.kerf # y length to split
                _x = 0 # number of holes on each x side (not counting the corner holes)
                _y = 0 # number of holes on each y side (not counting the corner holes)
                free = (holes-4)/2 # number of free holes to be placed on either x or y sides
                for f in range(free): # loop through the available holes and place them
                    if x/(_x+1) == y/(_y+1): # if equal, add the hole to the longer side
                        if x >= y:
                            _x += 1
                        else:
                            _y += 1
                    elif x/(_x+1) > y/(_y+1):
                        _x += 1
                    else:
                        _y += 1
                self.case['x_holes'] = _x
                self.case['y_holes'] = _y


    # take a set of points and rotate them 'r' degrees around 'a'
    def rotate_points(self, points, r, a):
        result = []
        for p in points:
            px = math.cos(math.radians(r)) * (p[0]-a[0]) - math.sin(math.radians(r)) * (p[1]-a[1]) + a[0]
            py = math.sin(math.radians(r)) * (p[0]-a[0]) + math.cos(math.radians(r)) * (p[1]-a[1]) + a[1]
            result.append((px,py))
        return result


    # cut a switch opening with center 'c' defined by the 'key'
    def cut_switch(self, p, c, key=None, layer=SWITCH_LAYER):
        """Cut a switch opening

        p: The plate object

        c: Center of the switch

        key: A dictionary describing this key, if not provided a 1u key at 0,0 will be used.

        layer: The layer we're cutting
        """
        if not key:
            key = {}

        w = key['w'] if 'w' in key else 1
        h = key['h'] if 'h' in key else 1
        t = key['_t'] if '_t' in key and key['_t'] in range(4) else self.switch_type
        s = key['_s'] if '_s' in key and key['_s'] in range(4) else self.stab_type
        k = key['_k']/2 if '_k' in key else self.kerf
        r = key['_r'] if '_r' in key else None
        rs = key['_rs'] if '_rs' in key else None
        offset = 0

        # cut switch cutout
        rotate = None
        if 'h' in key and h > w:
            rotate = True
        points = []

        # Standard locations with no offset
        mx_height = 7
        mx_width = 7
        alps_height = 6.4
        alps_width = 7.8
        wing_inside = 2.9
        wing_outside = 6
        # FIXME: Use more descriptive names here
        stab_1 = 4.73
        stab_2 = 8.575
        stab_cherry_top_x = 5.53
        stab_4 = 10.3
        stab_5 = 6.45
        stab_6 = 13.6
        stab_7 = 15.225
        stab_y_wire = 2.3
        stab_9 = 16.1
        stab_cherry_wing_bottom_x = 0.5
        stab_cherry_bottom_x = 6.77
        stab_12 = 7.75
        stab_13 = 5.97
        stab_cherry_bottom_wing_bottom_y = 7.97
        stab_cherry_half_width = 3.325
        stab_cherry_bottom_wing_half_width = 1.65
        stab_cherry_outside_x = 4.2
        alps_stab_top_y = 4
        alps_stab_bottom_y = 9
        alps_stab_inside_x = 16.7 if w == 2.75 else 12.7
        alps_stab_ouside_x = alps_stab_inside_x + 2.7

        if layer is TOP_LAYER:
            # Cut out openings the size of keycaps
            t = 0
            s = 1
            mx_width = (self.u1/2+0.5) * w
            mx_height = self.u1/2+0.5
        elif layer is REINFORCING_LAYER:
            offset = 1.25
            mx_height += offset
            mx_width += offset
            alps_height += offset
            alps_width += offset
            wing_inside += offset
            wing_outside += offset
            stab_1 += offset
            stab_2 += offset
            stab_cherry_top_x += offset
            stab_4 += offset
            stab_5 += offset
            stab_6 += offset
            stab_7 += offset
            stab_y_wire += offset
            stab_9 += offset
            stab_cherry_wing_bottom_x += offset
            stab_cherry_bottom_x += offset
            stab_12 += offset
            stab_13 += offset
            stab_cherry_bottom_wing_bottom_y += offset
            stab_cherry_half_width += offset
            stab_cherry_bottom_wing_half_width += offset
            stab_cherry_outside_x += offset
            alps_stab_top_y -= offset
            alps_stab_bottom_y += offset
            alps_stab_inside_x -= offset
            alps_stab_ouside_x += offset

        # Figure out our stabs now in case the switch itself is offset.
        l = w
        if rotate:
            l = h
        x, center_offset = (11.95, 0)  # default to a 2unit stabilizer if not found...
        stab_size = '%s' % (str(l).replace('.', '').ljust(3, '0') if l < 10 else str(l).replace('.', '').ljust(4, '0'))
        if stab_size in self.stabs:
            x, center_offset = self.stabs[stab_size]

        if center_offset > 0:
            # Move to cut the offset switch hole
            p = p.center(center_offset, 0)

        if t == 0: # standard square switch
            points = [
                (mx_width-k+self.grow_x,-mx_height+k-self.grow_y), (mx_width-k+self.grow_x,mx_height-k+self.grow_y),
                (-mx_width+k-self.grow_x,mx_height-k+self.grow_y), (-mx_width+k-self.grow_x,-mx_height+k-self.grow_y),
                (mx_width-k+self.grow_x,-mx_height+k-self.grow_y)
            ]
        elif t == 1: # mx and alps compatible switch, mx can open
            points = [
                (mx_width-k,-mx_height+k), (mx_width-k,-alps_height+k), (alps_width-k,-alps_height+k),
                (alps_width-k,alps_height-k), (mx_width-k,alps_height-k), (mx_width-k,mx_height-k),
                (-mx_width+k,mx_height-k), (-mx_width+k,alps_height-k), (-alps_width+k,alps_height-k),
                (-alps_width+k,-alps_height+k), (-mx_width+k,-alps_height+k), (-mx_width+k,-mx_height+k),
                (mx_width-k,-mx_height+k)
            ]
        elif t == 2: # mx switch can open (side wings)
            points = [
                (mx_width-k,-mx_height+k), (mx_width-k,-wing_outside+k), (alps_width-k,-wing_outside+k),
                (alps_width-k,-wing_inside-k), (mx_width-k,-wing_inside-k), (mx_width-k,wing_inside+k),
                (alps_width-k,wing_inside+k), (alps_width-k,wing_outside-k), (mx_width-k,wing_outside-k),
                (mx_width-k,mx_height-k), (-mx_width+k,mx_height-k), (-mx_width+k,wing_outside-k),
                (-alps_width+k,wing_outside-k), (-alps_width+k,wing_inside+k), (-mx_width+k,wing_inside+k),
                (-mx_width+k,-wing_inside-k), (-alps_width+k,-wing_inside-k), (-alps_width+k,-wing_outside+k),
                (-mx_width+k,-wing_outside+k), (-mx_width+k,-mx_height+k), (mx_width-k,-mx_height+k)
            ]
        elif t == 3: # rotatable mx switch can open both ways (side and top/bottom wings)
            points = [
                (mx_width-k,-mx_height+k), (mx_width-k,-wing_outside+k), (alps_width-k,-wing_outside+k),
                (alps_width-k,-wing_inside-k), (mx_width-k,-wing_inside-k), (mx_width-k,wing_inside+k),
                (alps_width-k,wing_inside+k), (alps_width-k,wing_outside-k), (mx_width-k,wing_outside-k),
                (mx_width-k,mx_height-k), (wing_outside-k,mx_height-k), (wing_outside-k,alps_width-k),
                (wing_inside+k,alps_width-k), (wing_inside+k,mx_height-k), (-wing_inside-k,mx_height-k),
                (-wing_inside-k,alps_width-k), (-wing_outside+k,alps_width-k), (-wing_outside+k,7-k),
                (-mx_width+k,mx_height-k), (-mx_width+k,wing_outside-k), (-alps_width+k,wing_outside-k),
                (-alps_width+k,wing_inside+k), (-mx_width+k,wing_inside+k), (-mx_width+k,-wing_inside-k),
                (-alps_width+k,-wing_inside-k), (-alps_width+k,-wing_outside+k), (-mx_width+k,-wing_outside+k),
                (-mx_width+k,-mx_height+k), (-wing_outside+k,-mx_height+k), (-wing_outside+k,-alps_width+k),
                (-wing_inside-k,-alps_width+k), (-wing_inside-k,-mx_height+k), (wing_inside+k,-mx_height+k),
                (wing_inside+k,-alps_width+k), (wing_outside-k,-alps_width+k), (wing_outside-k,-mx_height+k),
                (mx_width-k,-mx_height+k)
            ]
        elif t == 4: # alps compatible switch, not MX compatible
            points = [
                (alps_width-k,-alps_height+k),
                (alps_width-k,alps_height-k),
                (-alps_width+k,alps_height-k), (-alps_width+k,-alps_height+k),
                (alps_width-k,-alps_height+k),
            ]

        if rotate:
            points = self.rotate_points(points, 90, (0,0))
        if r:
            points = self.rotate_points(points, r, (0,0))

        p = self.center(p, c[0] ,c[1]).polyline(points).cutThruAll()

        if center_offset > 0:
            # Move back to the center of the key
            p = p.center(-center_offset, 0)

        # cut 2 unit stabilizer cutout
        if layer == TOP_LAYER:
            self.x_off += c[0]
            return p

        elif (w >= 2 and w < 3) or (rotate and h >= 2 and h < 3): # 2 unit stabilizer
            if s == 0:
                # modified mx cherry spec 2u stabilizer to support costar
                points = [
                    (mx_width-k,-mx_height+k), (mx_width-k,-stab_1+k), (stab_2+k,-stab_1+k), (stab_2+k,-stab_cherry_top_x+k),
                    (stab_4+k,-stab_cherry_top_x+k), (stab_4+k,-stab_5+k), (stab_6-k,-stab_5+k), (stab_6-k,-stab_cherry_top_x+k),
                    (stab_7-k,-stab_cherry_top_x+k), (stab_7-k,-stab_y_wire+k), (stab_9-k,-stab_y_wire+k), (stab_9-k,stab_cherry_wing_bottom_x-k),
                    (stab_7-k,stab_cherry_wing_bottom_x-k), (stab_7-k,stab_cherry_bottom_x-k), (stab_6-k,stab_cherry_bottom_x-k), (stab_6-k,stab_12-k),
                    (stab_4+k,stab_12-k), (stab_4+k,stab_cherry_bottom_x-k), (stab_2+k,stab_cherry_bottom_x-k), (stab_2+k,stab_13-k),
                    (mx_width-k,stab_13-k), (mx_width-k,mx_height-k), (-mx_width+k,mx_height-k), (-mx_width+k,stab_13-k),
                    (-stab_2-k,stab_13-k), (-stab_2-k,stab_cherry_bottom_x-k), (-stab_4-k,stab_cherry_bottom_x-k), (-stab_4-k,stab_12-k),
                    (-stab_6+k,stab_12-k), (-stab_6+k,stab_cherry_bottom_x-k), (-stab_7+k,stab_cherry_bottom_x-k), (-stab_7+k,stab_cherry_wing_bottom_x-k),
                    (-stab_9+k,stab_cherry_wing_bottom_x-k), (-stab_9+k,-stab_y_wire+k), (-stab_7+k,-stab_y_wire+k), (-stab_7+k,-stab_cherry_top_x+k),
                    (-stab_6+k,-stab_cherry_top_x+k), (-stab_6+k,-stab_5+k), (-stab_4-k,-stab_5+k), (-stab_4-k,-stab_cherry_top_x+k),
                    (-stab_2-k,-stab_cherry_top_x+k), (-stab_2-k,-stab_1+k), (-mx_width+k,-stab_1+k), (-mx_width+k,-mx_height+k),
                    (mx_width-k,-mx_height+k)
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rs:
                    points = self.rotate_points(points, rs, (0,0))
                p = p.polyline(points).cutThruAll()
            elif s == 1:
                # cherry spec 2u stabilizer
                points = [
                    (mx_width-k,-mx_height+k), (mx_width-k,-stab_1+k), (stab_2+k,-stab_1+k), (stab_2+k,-stab_cherry_top_x+k),
                    (stab_7-k,-stab_cherry_top_x+k), (stab_7-k,-stab_y_wire+k), (stab_9-k,-stab_y_wire+k), (stab_9-k,stab_cherry_wing_bottom_x-k),
                    (stab_7-k,stab_cherry_wing_bottom_x-k), (stab_7-k,stab_cherry_bottom_x-k), (stab_6-k,stab_cherry_bottom_x-k), (stab_6-k,stab_cherry_bottom_wing_bottom_y-k),
                    (stab_4+k,stab_cherry_bottom_wing_bottom_y-k), (stab_4+k,stab_cherry_bottom_x-k), (stab_2+k,stab_cherry_bottom_x-k), (stab_2+k,stab_13-k),
                    (mx_width-k,stab_13-k), (mx_width-k,mx_height-k), (-mx_width+k,mx_height-k), (-mx_width+k,stab_13-k),
                    (-stab_2-k,stab_13-k), (-stab_2-k,stab_cherry_bottom_x-k), (-stab_4-k,stab_cherry_bottom_x-k), (-stab_4-k,stab_cherry_bottom_wing_bottom_y-k),
                    (-stab_6+k,stab_cherry_bottom_wing_bottom_y-k), (-stab_6+k,stab_cherry_bottom_x-k), (-stab_7+k,stab_cherry_bottom_x-k), (-stab_7+k,stab_cherry_wing_bottom_x-k),
                    (-stab_9+k,stab_cherry_wing_bottom_x-k), (-stab_9+k,-stab_y_wire+k), (-stab_7+k,-stab_y_wire+k), (-stab_7+k,-stab_cherry_top_x+k),
                    (-stab_2-k,-stab_cherry_top_x+k), (-stab_2-k,-stab_1+k), (-mx_width+k,-stab_1+k), (-mx_width+k,-mx_height+k),
                    (mx_width-k,-mx_height+k)
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rs:
                    points = self.rotate_points(points, rs, (0,0))
                p = p.polyline(points).cutThruAll()
            elif s == 2:
                # costar stabilizers only
                points_l = [
                    (-stab_4-k,-stab_5+k), (-stab_6+k,-stab_5+k), (-stab_6+k,stab_12-k), (-stab_4-k,stab_12-k),
                    (-stab_4-k,-stab_5+k)
                ]
                points_r = [
                    (stab_4+k,-stab_5+k), (stab_6-k,-stab_5+k), (stab_6-k,stab_12-k), (stab_4+k,stab_12-k),
                    (stab_4+k,-stab_5+k)
                ]
                if rotate:
                    points_l = self.rotate_points(points_l, 90, (0,0))
                    points_r = self.rotate_points(points_r, 90, (0,0))
                if rs:
                    points_l = self.rotate_points(points_l, rs, (0,0))
                    points_r = self.rotate_points(points_r, rs, (0,0))
                p = p.polyline(points_l).cutThruAll()
                p = p.polyline(points_r).cutThruAll()
            elif s in (3, 4):
                # Alps stabilizers
                points_r = [
                    (alps_stab_inside_x+k, alps_stab_top_y+k), (alps_stab_ouside_x-k, alps_stab_top_y+k),
                    (alps_stab_ouside_x-k, alps_stab_bottom_y-k), (alps_stab_inside_x+k, alps_stab_bottom_y-k),
                    (alps_stab_inside_x+k, alps_stab_top_y+k)
                ]
                points_l = [
                    (-alps_stab_inside_x+k, alps_stab_top_y+k), (-alps_stab_ouside_x-k, alps_stab_top_y+k),
                    (-alps_stab_ouside_x-k, alps_stab_bottom_y-k), (-alps_stab_inside_x+k, alps_stab_bottom_y-k),
                    (-alps_stab_inside_x+k, alps_stab_top_y+k)
                ]

                if rotate:
                    points_l = self.rotate_points(points_l, 90, (0,0))
                    points_r = self.rotate_points(points_r, 90, (0,0))
                if rs:
                    points_l = self.rotate_points(points_l, rs, (0,0))
                    points_r = self.rotate_points(points_r, rs, (0,0))
                p = p.polyline(points_l).cutThruAll()
                p = p.polyline(points_r).cutThruAll()
            else:
                log.error('Unknown stab type %s! No stabilizer cut', s)

        # cut spacebar stabilizer cutout
        elif (w >= 3) or (rotate and h >= 3):
            if s == 0:
                # modified mx cherry spec stabilizer to support costar
                points = [
                    (x-stab_cherry_half_width+k,-stab_y_wire+k),
                    (x-stab_cherry_half_width+k,-stab_cherry_top_x+k),
                    (x-stab_cherry_bottom_wing_half_width+k,-stab_cherry_top_x+k),
                    (x-stab_cherry_bottom_wing_half_width+k,-stab_5+k),
                    (x+stab_cherry_bottom_wing_half_width-k,-stab_5+k),
                    (x+stab_cherry_bottom_wing_half_width-k,-stab_cherry_top_x+k),
                    (x+stab_cherry_half_width-k,-stab_cherry_top_x+k),
                    (x+stab_cherry_half_width-k,-stab_y_wire+k),
                    (x+stab_cherry_outside_x-k,-stab_y_wire+k),
                    (x+stab_cherry_outside_x-k,stab_cherry_wing_bottom_x-k),
                    (x+stab_cherry_half_width-k,stab_cherry_wing_bottom_x-k),
                    (x+stab_cherry_half_width-k,stab_cherry_bottom_x-k),
                    (x+stab_cherry_bottom_wing_half_width-k,stab_cherry_bottom_x-k),
                    (x+stab_cherry_bottom_wing_half_width-k,stab_12-k),
                    (x-stab_cherry_bottom_wing_half_width+k,stab_12-k),
                    (x-stab_cherry_bottom_wing_half_width+k,stab_cherry_bottom_x-k),
                    (x-stab_cherry_half_width+k,stab_cherry_bottom_x-k),
                    (x-stab_cherry_half_width+k,stab_y_wire-k),
                    (-x+stab_cherry_half_width-k,stab_y_wire-k),
                    (-x+stab_cherry_half_width-k,stab_cherry_bottom_x-k),
                    (-x+stab_cherry_bottom_wing_half_width-k,stab_cherry_bottom_x-k),
                    (-x+stab_cherry_bottom_wing_half_width-k,stab_12-k),
                    (-x-stab_cherry_bottom_wing_half_width+k,stab_12-k),
                    (-x-stab_cherry_bottom_wing_half_width+k,stab_cherry_bottom_x-k),
                    (-x-stab_cherry_half_width+k,stab_cherry_bottom_x-k),
                    (-x-stab_cherry_half_width+k,stab_cherry_wing_bottom_x-k),
                    (-x-stab_cherry_outside_x+k,stab_cherry_wing_bottom_x-k),
                    (-x-stab_cherry_outside_x+k,-stab_y_wire+k),
                    (-x-stab_cherry_half_width+k,-stab_y_wire+k),
                    (-x-stab_cherry_half_width+k,-stab_cherry_top_x+k),
                    (-x-stab_cherry_bottom_wing_half_width+k,-stab_cherry_top_x+k),
                    (-x-stab_cherry_bottom_wing_half_width+k,-stab_5+k),
                    (-x+stab_cherry_bottom_wing_half_width-k,-stab_5+k),
                    (-x+stab_cherry_bottom_wing_half_width-k,-stab_cherry_top_x+k),
                    (-x+stab_cherry_half_width-k,-stab_cherry_top_x+k),
                    (-x+stab_cherry_half_width-k,-stab_y_wire+k),
                    (x-stab_cherry_half_width+k,-stab_y_wire+k)
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rs:
                    points = self.rotate_points(points, rs, (0,0))
                p = p.polyline(points).cutThruAll()
            elif s == 1:
                # cherry spec spacebar stabilizer
                points = [
                    (x - stab_cherry_half_width + k, -stab_y_wire + k),
                    (x - stab_cherry_half_width + k, -stab_cherry_top_x + k),
                    (x + stab_cherry_half_width - k, -stab_cherry_top_x + k),
                    (x + stab_cherry_half_width - k, -stab_y_wire + k),
                    (x + stab_cherry_outside_x - k, -stab_y_wire + k),
                    (x + stab_cherry_outside_x - k, stab_cherry_wing_bottom_x - k),
                    (x + stab_cherry_half_width - k, stab_cherry_wing_bottom_x - k),
                    (x + stab_cherry_half_width - k, stab_cherry_bottom_x - k),
                    (x + stab_cherry_bottom_wing_half_width - k, stab_cherry_bottom_x - k),
                    (x + stab_cherry_bottom_wing_half_width - k, stab_cherry_bottom_wing_bottom_y - k),
                    (x - stab_cherry_bottom_wing_half_width + k, stab_cherry_bottom_wing_bottom_y - k),
                    (x - stab_cherry_bottom_wing_half_width + k, stab_cherry_bottom_x - k),
                    (x - stab_cherry_half_width + k, stab_cherry_bottom_x - k),
                    (x - stab_cherry_half_width + k, stab_y_wire - k),
                    (-x + stab_cherry_half_width - k, stab_y_wire - k),
                    (-x + stab_cherry_half_width - k, stab_cherry_bottom_x - k),
                    (-x + stab_cherry_bottom_wing_half_width - k, stab_cherry_bottom_x - k),
                    (-x + stab_cherry_bottom_wing_half_width - k, stab_cherry_bottom_wing_bottom_y - k),
                    (-x - stab_cherry_bottom_wing_half_width + k, stab_cherry_bottom_wing_bottom_y - k),
                    (-x - stab_cherry_bottom_wing_half_width + k, stab_cherry_bottom_x - k),
                    (-x - stab_cherry_half_width + k, stab_cherry_bottom_x - k),
                    (-x - stab_cherry_half_width + k, stab_cherry_wing_bottom_x - k),
                    (-x - stab_cherry_outside_x + k, stab_cherry_wing_bottom_x - k),
                    (-x - stab_cherry_outside_x + k, -stab_y_wire + k),
                    (-x - stab_cherry_half_width + k, -stab_y_wire + k),
                    (-x - stab_cherry_half_width + k, -stab_cherry_top_x + k),
                    (-x + stab_cherry_half_width - k, -stab_cherry_top_x + k),
                    (-x + stab_cherry_half_width - k, -stab_y_wire + k),
                    (x - stab_cherry_half_width + k, -stab_y_wire + k),
                ]
                points_l = [
                    (0, -5.53),
                    (50.95, -5.53),
                    (50.95, -2.3),
                    (51.825, -2.3),
                    (51.825, 0.5),
                    (50.95, 0.5),
                    (50.95, 6.77),
                    (49.275, 6.77),
                    (49.275, 7.97),
                    (45.975, 7.97),
                    (45.975, 6.77),
                    (44.3, 6.77),
                    (44.3, 2.3),
                    (0, 2.3)
                ]
                points_l = [
                    (0, -2.3),
                    (44.3, -2.3),
                    (44.3, -5.53),
                    (51.825, -5.53),
                    (51.825, 7.97),
                    (44.3, 7.97),
                    (44.3, 2.3),
                    (0, 2.3),
                    (0, -2.3)
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rs:
                    points = self.rotate_points(points, rs, (0,0))
                p = p.polyline(points).cutThruAll()
            elif s in (2, 3):
                # costar stabilizers only
                points_l = [
                    (-x+stab_cherry_bottom_wing_half_width-k,-stab_5+k), (-x-stab_cherry_bottom_wing_half_width+k,-stab_5+k), (-x-stab_cherry_bottom_wing_half_width+k,stab_12-k),
                    (-x+stab_cherry_bottom_wing_half_width-k,stab_12-k), (-x+stab_cherry_bottom_wing_half_width-k,-stab_5+k)
                ]
                points_r = [
                    (x-stab_cherry_bottom_wing_half_width+k,-stab_5+k), (x+stab_cherry_bottom_wing_half_width-k,-stab_5+k), (x+stab_cherry_bottom_wing_half_width-k,stab_12-k),
                    (x-stab_cherry_bottom_wing_half_width+k,stab_12-k), (x-stab_cherry_bottom_wing_half_width+k,-stab_5+k)
                ]
                if rotate:
                    points_l = self.rotate_points(points_l, 90, (0,0))
                    points_r = self.rotate_points(points_r, 90, (0,0))
                if rs:
                    points_l = self.rotate_points(points_l, rs, (0,0))
                    points_r = self.rotate_points(points_r, rs, (0,0))
                p = p.polyline(points_l).cutThruAll()
                p = p.polyline(points_r).cutThruAll()
            elif s == 4:
                # Alps stabilizers only
                # FIXME: Write this
                log.error('Vintage alps stabilizers for spacebar not implemented!')
            else:
                log.error('Unknown stab type %s! No stabilizer cut', s)

        self.x_off += c[0]
        return p


    # sets the center and also records the relative distance it moved in relation to 'origin'
    def center(self, p, x, y):
        _x = self.origin[0]
        _y = self.origin[1]
        self.origin = (_x+x, _y+y)
        return p.center(x, y)


    def __repr__(self):
        '''Print out all Plate object configuration settings.'''

        settings = {}

        settings['plate_layout'] = self.layout
        settings['switch_type'] = self.switch_type
        settings['stabilizer_type'] = self.stab_type
        settings['case_type_and_holes'] = self.case
        settings['width_padding'] = self.x_pad
        settings['height_padding'] = self.y_pad
        settings['pcb_width_padding'] = self.x_pcb_pad
        settings['pcb_height_padding'] = self.y_pcb_pad
        settings['plate_corners'] = self.corners
        settings['kerf'] = self.kerf
        # XXX line colour?

        return json.dumps(settings, sort_keys=True, indent=4, separators=(',', ': '))



    def export(self, p, result, label, data_hash, config):
        # export the plate to different file formats
        log.info("Exporting %s layer for %s" % (label, data_hash))
        # draw the part so we can export it
        Part.show(p.val().wrapped)
        doc = FreeCAD.ActiveDocument
        # export the drawing into different formats
        pwd_len = len(config['app']['pwd']) # the absolute part of the working directory (aka - outside the web space)
        result['exports'][label] = []
        if 'js' in result['formats']:
            with open("%s/%s_%s.js" % (config['app']['export'], label, data_hash), "w") as f:
                cadquery.exporters.exportShape(p, 'TJS', f)
                result['exports'][label].append({'name':'js', 'url':'%s/%s_%s.js' % (config['app']['export'][pwd_len:], label, data_hash)})
                log.info("Exported 'JS'")
        if 'brp' in result['formats']:
            Part.export(doc.Objects, "%s/%s_%s.brp" % (config['app']['export'], label, data_hash))
            result['exports'][label].append({'name':'brp', 'url':'%s/%s_%s.brp' % (config['app']['export'][pwd_len:], label, data_hash)})
            log.info("Exported 'BRP'")
        if 'stp' in result['formats']:
            Part.export(doc.Objects, "%s/%s_%s.stp" % (config['app']['export'], label, data_hash))
            result['exports'][label].append({'name':'stp', 'url':'%s/%s_%s.stp' % (config['app']['export'][pwd_len:], label, data_hash)})
            log.info("Exported 'STP'")
        if 'stl' in result['formats']:
            Mesh.export(doc.Objects, "%s/%s_%s.stl" % (config['app']['export'], label, data_hash))
            result['exports'][label].append({'name':'stl', 'url':'%s/%s_%s.stl' % (config['app']['export'][pwd_len:], label, data_hash)})
            log.info("Exported 'STL'")
        if 'dxf' in result['formats']:
            importDXF.export(doc.Objects, "%s/%s_%s.dxf" % (config['app']['export'], label, data_hash))
            result['exports'][label].append({'name':'dxf', 'url':'%s/%s_%s.dxf' % (config['app']['export'][pwd_len:], label, data_hash)})
            log.info("Exported 'DXF'")
        if 'svg' in result['formats']:
            importSVG.export(doc.Objects, "%s/%s_%s.svg" % (config['app']['export'], label, data_hash))
            result['exports'][label].append({'name':'svg', 'url':'%s/%s_%s.svg' % (config['app']['export'][pwd_len:], label, data_hash)})
            log.info("Exported 'SVG'")
        if 'json' in result['formats'] and label == SWITCH_LAYER:
            with open("%s/%s_%s.json" % (config['app']['export'], label, data_hash), 'w') as json_file:
                json_file.write(repr(self))
            result['exports'][label].append({'name':'json', 'url':'%s/%s_%s.json' % (config['app']['export'][pwd_len:], label, data_hash)})
            log.info("Exported 'JSON'")
        # remove all the documents from the view before we move on
        for o in doc.Objects:
            doc.removeObject(o.Label)


# take the input from the webserver and instantiate and draw the plate
def build(data_hash, data, config):
    # create the result object
    p = Plate(**data)
    result = {
        'has_layers': len(p.layers) > 1,
        'plates': p.layers,
        'formats': p.formats,
        'exports': p.exports
    }
    result = p.draw(result, data_hash, config) # draw the plate
    log.info("Finished drawing: %s" % (data_hash))
    return result # return the metadata result to the webserver


