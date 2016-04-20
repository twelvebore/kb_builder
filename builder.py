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

# Some notes that have helped skullydazed make sense of this code as an outsider
#
# * Kerf is used only to change the line position. Positioning center should
#   be done without taking kerf into account- or, in some cases, undoing the
#   kerf adjustment.
# * Sometimes FreeCAD wants things done in a certain order. I haven't been able
#   to determine why. If you have FreeCAD throwing obscure errors at you try
#   changing the order of operations.

import json
import logging
import math

import config

log = logging.getLogger()

import FreeCAD
import cadquery
import importDXF
import importSVG
import Mesh
import Part


# Constants
KEY_UNIT = 19.05  # How many MM wide a 1u key is
STABILIZERS = {
    # size: (width_between_center, switch_offset)
    2: (11.95, 0),
    3: (19.05, 0),
    4: (28.575, 0),
    4.5: (34.671, 0),
    5.5: (42.8625, 0),
    6: (47.625, 9.525),
    6.25: (50, 0),
    6.5: (52.38, 0),
    7: (57.15, 0),
    8: (66.675, 0),
    9: (66.675, 0),
    10: (66.675, 0)
}

class KeyboardCase(object):
    def __init__(self, keyboard_layout, export_basename, kerf=0.0,
                 case_type=None, corner_type='round', width_padding=0,
                 height_padding=0, usb_inner_width=10, usb_outer_width=10,
                 usb_height=7.5, stab_type='cherry', corners=0,
                 switch_type='mx', usb_offset=0, pcb_height_padding=0,
                 pcb_width_padding=0, mount_holes_num=0, mount_holes_size=0,
                 thickness=1.5, holes=None, reinforcing=False, oversize=None,
                 oversize_distance=4, formats=None, foot_holes=None,
                 foot_count=None, foot_hole_diameter=3, foot_hole_square=9,
                 usb_layers=None):
        # User settable things
        self.export_basename = export_basename
        self.case = {'type': case_type}
        self.corner_type = corner_type
        self.corners = corners
        self.formats = formats if formats else ['dxf']
        self.foot_holes = foot_holes if foot_holes else []
        self.foot_count = int(foot_count) if foot_count else len(self.foot_holes)
        self.foot_hole_diameter = foot_hole_diameter - kerf/2
        self.foot_hole_square = foot_hole_square - kerf
        self.kerf = kerf / 2
        self.keyboard_layout = keyboard_layout
        self.holes = holes if holes else []
        self.oversize = oversize if oversize else []
        self.oversize_distance = oversize_distance
        self.stab_type = stab_type
        self.switch_type = switch_type
        self.thickness = thickness
        self.usb_inner_width = usb_inner_width - kerf
        self.usb_outer_width = usb_outer_width - kerf
        self.usb_height = usb_height - kerf
        self.usb_offset = usb_offset
        self.usb_layers = usb_layers if usb_layers else ['open']
        self.x_pad = width_padding
        self.x_pcb_pad = pcb_width_padding / 2
        self.y_pad = height_padding
        self.y_pcb_pad = pcb_height_padding / 2

        # Sanity checks
        if switch_type not in ('mx', 'alpsmx', 'mx-open', 'mx-open-rotatable', 'alps'):
            log.error('Unknown switch type %s, defaulting to mx!', switch_type)
            self.switch_type = 'mx'

        if stab_type not in ('cherry', 'costar', 'cherry-costar', 'matias', 'alps'):
            log.error('Unknown stabilizer type %s, defaulting to "cherry"!', stab_type)
            self.stab_type = 'cherry'

        # Plate state info
        self.UOM = "mm"
        self.exports = {}
        self.grow_y = 0
        self.grow_x = 0
        self.height = 0
        self.inside_height = 0
        self.inside_width = 0
        self.layers = ['switch']
        self.layout = []
        self.origin = (0,0)
        self.width = 0
        self.x_off = 0

        # Initialize the case
        if self.case['type'] == 'poker':
            if mount_holes_size > 0:
                self.case = {'type': 'poker', 'hole_diameter': mount_holes_size}
        elif self.case['type'] == 'sandwich':
            self.layers += ['top', 'reinforcing', 'open', 'closed', 'simple', 'bottom']
            if mount_holes_num > 0 and mount_holes_size > 0:
                self.case = {'type': 'sandwich', 'holes': mount_holes_num, 'hole_diameter': mount_holes_size, 'x_holes':0, 'y_holes':0}
        elif self.case['type']:
            log.error('Unknown case type: %s, skipping case generation', self.case['type'])

        if reinforcing and 'reinforcing' not in self.layers:
            self.layers.append('reinforcing')

        # Determine the size of each key
        self.parse_layout()

    def create_bottom_layer(self, oversize=0):
        """Returns a copy of the bottom layer ready to export.
        """
        plate = self.init_plate(oversize=oversize)
        plate = self.cut_feet_holes(plate)
        plate = self.cut_usb_hole(plate, 'bottom', oversize=oversize)

        return plate

    def create_closed_layer(self, oversize=0):
        """Returns a copy of the closed layer ready to export.

        We stash nifty things like the feet in the closed layer.
        """
        FOOT_POINTS = [
            # Feet that are drawn in the closed/open layers. Sized for 9-10mm M4.
            (3-self.kerf,0-self.kerf),                  # Upper left corner
            (9+self.kerf,0-self.kerf),                  # Upper right corner start
            (14+self.kerf,4-self.kerf),                 # Upper right corner end
            (5+self.kerf,91+self.kerf),                 # Lower right corner
            (3-self.kerf,91+self.kerf),                 # Lower left corner
            (3-self.kerf,71+self.kerf),                 # Lower right of key
            (0-self.kerf,71+self.kerf),                 # Lower left of key
            (0-self.kerf,62-self.kerf),                 # Top of the key for the bottom plate
            (3-self.kerf,62-self.kerf),                 # Inside corner of the key
            (3-self.kerf,7.5-self.kerf), (5+self.kerf,7.5-self.kerf),       # Start of the nut cutout
            (5+self.kerf,9.1-self.kerf), (7.2-self.kerf,9.1-self.kerf),       # Bottom edge of the nut cutout
            (7.2-self.kerf,7.5-self.kerf), (9.2-self.kerf,7.5-self.kerf),  # Bottom-right edge of the screw cutout
            (9.2-self.kerf,4.5+self.kerf), (7.2-self.kerf,4.5+self.kerf),  # Top-right edge of the screw cutout
            (7.2-self.kerf,2.9+self.kerf), (5+self.kerf,2.9+self.kerf),         # Top edge of the nut cutout
            (5+self.kerf,4.5+self.kerf), (3-self.kerf,4.5+self.kerf),       # End of the screw cutout
            (3-self.kerf,0-self.kerf)                   # Upper left corner
        ]
        plate = self.init_plate(oversize=oversize)
        plate = self.recenter(plate)
        outline_points = [
            (self.inside_width/2, self.inside_height/2),
            (-self.inside_width/2, self.inside_height/2),
            (-self.inside_width/2, -self.inside_height/2),
            (self.inside_width/2, -self.inside_height/2),
            (self.inside_width/2, self.inside_height/2)
        ]
        left_edge = -((self.inside_width+self.kerf*2)/2)+5
        top_edge = -((self.inside_height+self.kerf*2)/2)+5

        plate = plate.polyline(outline_points)  # Cut the internal outline
        plate = plate.center(left_edge, top_edge)
        distance_moved = 0

        for i in range(self.foot_count):
            plate = plate.polyline(FOOT_POINTS).center(15, 0)  # Add a foot
            distance_moved += 15

        plate = plate.center(-left_edge-distance_moved,-top_edge).cutThruAll()  # Return to center and cut

        return plate

    def create_open_layer(self, oversize=0):
        """Returns a copy of the open layer ready to export.
        """
        plate = self.create_closed_layer(oversize=oversize)
        plate = self.cut_usb_hole(plate, 'open', oversize=oversize)

        return plate

    def create_switch_layer(self, layer):
        """Returns a copy of one of the switch based layers ready to export.

        The switch based layers are `switch`, `reinforcing`, and `top`.
        """
        prev_width = None
        prev_y_off = 0
        oversize = self.oversize_distance if layer in self.oversize else 0

        plate = self.init_plate(oversize=oversize)
        plate = self.center(plate, -self.width/2, -self.height/2) # move to top left of the plate

        if layer != 'top':
            # Put holes into switch/reinforcing plates
            plate = self.cut_switch_plate_holes(plate)

        for r, row in enumerate(self.layout):
            for k, key in enumerate(row):
                x, y, kx = 0, 0, 0
                if 'x' in key:
                    x = key['x']*KEY_UNIT
                    kx = x

                if 'y' in key and k == 0:
                    y = key['y']*KEY_UNIT

                if r == 0 and k == 0: # handle placement of the first key in first row
                    plate = self.center(plate, (key['w'] * KEY_UNIT / 2), (KEY_UNIT / 2))
                    x += (self.x_pad+self.x_pcb_pad)
                    y += (self.y_pad+self.y_pcb_pad)
                    # set x_off negative since the 'cut_switch' will append 'x' and we need to account for initial spacing
                    self.x_off = -(x - (KEY_UNIT/2 + key['w']*KEY_UNIT/2) - kx)
                elif k == 0: # handle changing rows
                    plate = self.center(plate, -self.x_off, KEY_UNIT) # move to the next row
                    self.x_off = 0 # reset back to the left side of the plate
                    x += KEY_UNIT/2 + key['w']*KEY_UNIT/2
                else: # handle all other keys
                    x += prev_width*KEY_UNIT/2 + key['w']*KEY_UNIT/2

                if prev_y_off != 0: # prev_y_off != 0
                    y += -prev_y_off
                    prev_y_off = 0

                if 'h' in key and key['h'] > 1: # deal with vertical keys
                    prev_y_off = key['h']*KEY_UNIT/2 - KEY_UNIT/2
                    y += prev_y_off

                # Cut the switch hole
                plate = self.cut_switch(plate, (x, y), key, layer)
                prev_width = key['w']

        plate = self.recenter(plate)
        plate = self.cut_usb_hole(plate, layer, oversize=oversize)
        return plate

    def cut_feet_holes(self, plate):
        """Cut the mounting points for the feet.
        """
        plate = self.recenter(plate)
        for foot_hole in self.foot_holes:
            points = [
                (self.foot_hole_square/2, self.foot_hole_square/2),
                (self.foot_hole_square/2, -self.foot_hole_square/2),
                (-self.foot_hole_square/2, -self.foot_hole_square/2),
                (-self.foot_hole_square/2, self.foot_hole_square/2),
                (self.foot_hole_square/2, self.foot_hole_square/2)
            ]
            plate = self.center(plate, -self.width/2, -self.height/2) # move to top left of the plate
            plate = self.center(plate, *foot_hole).circle(self.foot_hole_diameter/2).cutThruAll()  # Add screw hole
            plate = plate.center(0, 60).polyline(points).center(0, -60)  # Add square hole
            plate = self.recenter(plate).cutThruAll()

        return plate

    def cut_usb_hole(self, plate, layer, oversize=0):
        """Cut the opening that allows for the USB hole.
        """
        if layer not in self.usb_layers:
            return plate.cutThruAll()

        points = [
            (-self.usb_outer_width/2+self.usb_offset, -(self.y_pad+self.y_pcb_pad+self.kerf*2)/2-oversize/2),
            (self.usb_outer_width/2+self.usb_offset, -(self.y_pad+self.y_pcb_pad+self.kerf*2)/2-oversize/2),
            (self.usb_inner_width/2+self.usb_offset, (self.y_pad+self.y_pcb_pad)/2),
            (-self.usb_inner_width/2+self.usb_offset, (self.y_pad+self.y_pcb_pad)/2),
            (-self.usb_outer_width/2+self.usb_offset, -(self.y_pad+self.y_pcb_pad+self.kerf*2)/2-oversize/2)
        ]
        y_distance = -self.height / 2 + (self.y_pad + self.y_pcb_pad) / 2 - self.kerf*2
        plate = plate.center(0, y_distance).polyline(points)

        if layer == 'bottom':
            points = [
                (self.usb_inner_width/2+self.usb_offset, (self.y_pad+self.y_pcb_pad)/2),
                (-self.usb_inner_width/2+self.usb_offset, (self.y_pad+self.y_pcb_pad)/2),
                (-self.usb_inner_width/2+self.usb_offset, (self.y_pad+self.y_pcb_pad)/2+self.usb_height+self.kerf*3),  # 3 is a magic number
                (self.usb_inner_width/2+self.usb_offset, (self.y_pad+self.y_pcb_pad)/2+self.usb_height+self.kerf*3),   # yes it is
                (self.usb_inner_width/2+self.usb_offset, (self.y_pad+self.y_pcb_pad)/2)
            ]
            plate = plate.polyline(points)

        plate = plate.center(0, -y_distance).cutThruAll()

        return plate

    def cut_switch_plate_holes(self, plate):
        """Cut any holes specified for the switch/reinforcing plate.
        """
        for hole in self.holes:
            x, y, diameter = hole
            plate = plate.center(x, y).circle((diameter/2)-self.kerf).center(-x, -y).cutThruAll()

        return plate

    def parse_layout(self):
        """Parse the supplied layout to determine size and populate the properties of each key
        """
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
                layout_height += KEY_UNIT + row_height*KEY_UNIT;
            # hidden global features
            if isinstance(row, dict):
                if 'grow_y' in row and (type(row['grow_y']) == int or type(row['grow_y']) == float):
                    self.grow_y = row['grow_y']/2
                if 'grow_x' in row and (type(row['grow_x']) == int or type(row['grow_x']) == float):
                    self.grow_x = row['grow_x']/2
        self.width = layout_width*KEY_UNIT + 2*(self.x_pad+self.x_pcb_pad)
        self.height = layout_height + 2*(self.y_pad+self.y_pcb_pad)
        self.inside_height = self.height-self.y_pad*2-self.kerf*2
        self.inside_width = self.width-self.x_pad*2-self.kerf*2
        self.horizontal_edge = self.width / 2
        self.vertical_edge = self.height / 2

    def init_plate(self, oversize=0):
        """Return a basic plate with the features that are common to all layers.

        If oversize is greater than 0 the layer will be made that many mm larger than default, while keeping screws in the same position.
        """
        plate = cadquery.Workplane("front").box(self.width+self.kerf*2+oversize, self.height+self.kerf*2+oversize, self.thickness)

        # Cut the corners if necessary
        if self.corners > 0 and self.corner_type == 'round':
            plate = plate.edges("|Z").fillet(self.corners)

        plate = plate.faces("<Z").workplane()

        if self.corners > 0:
            if self.corner_type == 'beveled':
                # Lower right corner
                points = (
                    (self.horizontal_edge, self.vertical_edge - self.corners), (self.horizontal_edge, self.vertical_edge),
                    (self.horizontal_edge - self.corners, self.vertical_edge), (self.horizontal_edge, self.vertical_edge - self.corners),
                )
                plate = plate.polyline(points)
                # Lower left corner
                points = (
                    (-self.horizontal_edge, self.vertical_edge - self.corners), (-self.horizontal_edge, self.vertical_edge),
                    (-self.horizontal_edge + self.corners, self.vertical_edge), (-self.horizontal_edge, self.vertical_edge - self.corners),
                )
                plate = plate.polyline(points)
                # Upper right corner
                points = (
                    (self.horizontal_edge, -self.vertical_edge + self.corners), (self.horizontal_edge, -self.vertical_edge),
                    (self.horizontal_edge - self.corners, -self.vertical_edge), (self.horizontal_edge, -self.vertical_edge + self.corners),
                )
                plate = plate.polyline(points)
                # Upper left corner
                points = (
                    (-self.horizontal_edge, -self.vertical_edge + self.corners), (-self.horizontal_edge, -self.vertical_edge),
                    (-self.horizontal_edge + self.corners, -self.vertical_edge), (-self.horizontal_edge, -self.vertical_edge + self.corners),
                )
                plate = plate.polyline(points)
            elif self.corner_type != 'round':
                log.error('Unknown corner type %s!', self.corner_type)

        # Cut the mount holes in the plate
        if self.case['type'] == 'poker':
            hole_points = [(-139,9.2), (-117.3,-19.4), (-14.3,0), (48,37.9), (117.55,-19.4), (139,9.2)] # holes
            rect_center = (self.width/2) - (3.5/2)
            rect_points = [(rect_center,9.2), (-rect_center,9.2)] # edge slots
            rect_size = (3.5-self.kerf, 5-self.kerf) # edge slot cutout to edge
            for c in hole_points:
                plate = plate.center(c[0], c[1]).hole(self.case['hole_diameter'] - self.kerf).center(-c[0],-c[1])
            for c in rect_points:
                plate = plate.center(c[0], c[1]).rect(*rect_size).center(-c[0],-c[1])
        elif self.case['type'] == 'sandwich':
            plate = self.center(plate, -self.width/2 + self.kerf, -self.height/2 + self.kerf) # move to top left of the plate
            if 'holes' in self.case and self.case['holes'] >= 4 and 'x_holes' in self.case and 'y_holes' in self.case:
                self.layout_sandwich_holes()
                radius = self.case['hole_diameter']/2 - self.kerf
                x_gap = (self.width - 2*self.case['hole_diameter'] + 1)/(self.case['x_holes'] + 1)
                y_gap = (self.height - 2*self.case['hole_diameter'] + 1)/(self.case['y_holes'] + 1)
                hole_distance = self.case['hole_diameter'] - .5 - self.kerf
                plate = plate.center(hole_distance, hole_distance)
                for i in range(self.case['x_holes'] + 1):
                    plate = plate.center(x_gap,0).circle(radius)
                for i in range(self.case['y_holes'] + 1):
                    plate = plate.center(0,y_gap).circle(radius)
                for i in range(self.case['x_holes'] + 1):
                    plate = plate.center(-x_gap,0).circle(radius)
                for i in range(self.case['y_holes'] + 1):
                    plate = plate.center(0,-y_gap).circle(radius)
                plate = plate.center(-hole_distance, -hole_distance)
            plate = self.center(plate, self.width/2 - self.kerf, self.height/2 - self.kerf) # move to center of the plate
        elif not self.case['type'] or self.case['type'] == 'reinforcing':
            pass
        else:
            log.error('Unknown case type: %s', self.case['type'])

        self.origin = (0,0)
        return plate.cutThruAll()

    def layout_sandwich_holes(self):
        """Determine where screw holes should be placed.
        """
        if 'holes' in self.case and self.case['holes'] >= 4 and 'x_holes' in self.case and 'y_holes' in self.case:
            holes = int(self.case['holes'])
            if holes % 2 == 0 and holes >= 4: # holes needs to be even and the first 4 are put in the corners
                x = self.width + self.kerf*2   # x length to split
                y = self.height + self.kerf*2  # y length to split
                _x = 0                         # number of holes on each x side (not counting the corner holes)
                _y = 0                         # number of holes on each y side (not counting the corner holes)
                free = (holes-4)/2             # number of free holes to be placed on either x or y sides
                for f in range(free):          # loop through the available holes and place them
                    if x/(_x+1) == y/(_y+1):   # if equal, add the hole to the longer side
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
            else:
                log.error('Invalid hole configuration! Need at least 4 holes and must be divisible by 2!')

    def rotate_points(self, points, radians, rotate_point):
        """Rotate a sequence of points.

        points: the points to rotate

        radians: the number of degrees to rotate

        rotate_point: the coordinate to rotate around
        """
        def calculate_points(point):
            return (
                math.cos(math.radians(radians)) * (point[0]-rotate_point[0]) - math.sin(math.radians(radians)) * (point[1]-rotate_point[1]) + rotate_point[0],
                math.sin(math.radians(radians)) * (point[0]-rotate_point[0]) + math.cos(math.radians(radians)) * (point[1]-rotate_point[1]) + rotate_point[1]
            )

        return map(calculate_points, points)

    def cut_switch(self, plate, switch_coord, key=None, layer='switch'):
        """Cut a switch opening

        plate: The plate object

        switch_coord: Center of the switch

        key: A dictionary describing this key, if not provided a 1u key at 0,0 will be used.

        layer: The layer we're cutting
        """
        if not key:
            key = {}

        width = key['w'] if 'w' in key else 1
        height = key['h'] if 'h' in key else 1
        switch_type = key['_t'] if '_t' in key else self.switch_type
        stab_type = key['_s'] if '_s' in key else self.stab_type
        kerf = key['_k']/2 if '_k' in key else self.kerf
        rotate_key = key['_r'] if '_r' in key else None
        rotate_stab = key['_rs'] if '_rs' in key else None
        center_offset = key['_co'] if '_co' in key else False

        # cut switch cutout
        rotate = None
        if 'h' in key and height > width:
            rotate = True
        points = []

        # Standard locations with no offset
        mx_height = 7 - kerf
        mx_width = 7 - kerf
        alps_height = 6.4 - kerf
        alps_width = 7.8 - kerf
        wing_inside = 2.9 + kerf
        wing_outside = 6 - kerf
        # FIXME: Use more descriptive names here
        mx_stab_inside_y = 4.75 - kerf
        mx_stab_inside_x = 8.575 + kerf
        stab_cherry_top_x = 5.5 - kerf
        stab_4 = 10.3 + kerf
        stab_5 = 6.5 - kerf
        stab_6 = 13.6 - kerf
        mx_stab_outside_x = 15.225 - kerf
        stab_y_wire = 2.3 - kerf
        stab_bottom_y_wire = stab_y_wire - kerf
        stab_9 = 16.1 - kerf
        stab_cherry_wing_bottom_x = 0.5 - kerf
        stab_cherry_bottom_x = 6.75 - kerf
        stab_12 = 7.75 - kerf
        stab_13 = 6 - kerf
        stab_cherry_bottom_wing_bottom_y = 8 - kerf
        stab_cherry_half_width = 3.325 - kerf
        stab_cherry_bottom_wing_half_width = 1.65 - kerf
        stab_cherry_outside_x = 4.2 - kerf
        alps_stab_top_y = 4 + kerf
        alps_stab_bottom_y = 9 - kerf
        alps_stab_inside_x = (16.7 if width == 2.75 else 12.7) + kerf
        alps_stab_ouside_x = alps_stab_inside_x + 2.7 - kerf*2

        if layer == 'top':
            # Cut out openings the size of keycaps
            switch_type = 'mx'
            stab_type = 'cherry'
            if height > 1:
                mx_width = (((KEY_UNIT/2) * height) + 0.5) - kerf
            else:
                mx_width = (((KEY_UNIT/2) * width) + 0.5) - kerf
            mx_height = ((KEY_UNIT/2) + 0.5) - kerf
        elif layer == 'reinforcing':
            offset = 1
            mx_height += offset
            mx_width += offset
            alps_height += offset
            alps_width += offset
            wing_inside += offset
            wing_outside += offset
            mx_stab_inside_x += offset
            stab_cherry_top_x += 2.5 if offset < 2.5 else offset
            stab_y_wire = mx_stab_inside_y = stab_cherry_top_x
            stab_4 += offset
            stab_5 += offset
            stab_6 += offset
            mx_stab_outside_x += offset
            stab_9 += offset
            stab_cherry_bottom_x += 4.28 - kerf if offset < 4.28 else offset
            stab_cherry_wing_bottom_x = stab_bottom_y_wire = stab_cherry_bottom_wing_bottom_y = stab_13 = stab_12 = stab_cherry_bottom_x
            stab_cherry_half_width += offset
            stab_cherry_bottom_wing_half_width += offset
            stab_cherry_outside_x += offset
            alps_stab_top_y -= offset
            alps_stab_bottom_y += offset
            alps_stab_inside_x -= offset
            alps_stab_ouside_x += offset

        # Figure out our stabs now in case the switch itself is offset.
        length = width
        if rotate:
            length = height

        if length >= 2:
            x = STABILIZERS[length][0] if length in STABILIZERS else STABILIZERS[2][0]
            if not center_offset:
                center_offset = STABILIZERS[length][1] if length in STABILIZERS else 0

        if center_offset > 0:
            # If the user has specified an offset stab (EG, 6U) we first move
            # to cut the offset switch hole, and later will move back to cut
            # the stabilizer.
            plate = plate.center(center_offset, 0)

        if switch_type == 'mx':
            points = [
                (mx_width+self.grow_x,-mx_height-self.grow_y),
                (mx_width+self.grow_x,mx_height+self.grow_y),
                (-mx_width-self.grow_x,mx_height+self.grow_y),
                (-mx_width-self.grow_x,-mx_height-self.grow_y),
                (mx_width+self.grow_x,-mx_height-self.grow_y)
            ]
        elif switch_type == 'alpsmx':
            points = [
                (mx_width,-mx_height),
                (mx_width,-alps_height),
                (alps_width,-alps_height),
                (alps_width,alps_height),
                (mx_width,alps_height),
                (mx_width,mx_height),
                (-mx_width,mx_height),
                (-mx_width,alps_height),
                (-alps_width,alps_height),
                (-alps_width,-alps_height),
                (-mx_width,-alps_height),
                (-mx_width,-mx_height),
                (mx_width,-mx_height)
            ]
        elif switch_type == 'mx-open':
            points = [
                (mx_width,-mx_height),
                (mx_width,-wing_outside),
                (alps_width,-wing_outside),
                (alps_width,-wing_inside),
                (mx_width,-wing_inside),
                (mx_width,wing_inside),
                (alps_width,wing_inside),
                (alps_width,wing_outside),
                (mx_width,wing_outside),
                (mx_width,mx_height),
                (-mx_width,mx_height),
                (-mx_width,wing_outside),
                (-alps_width,wing_outside),
                (-alps_width,wing_inside),
                (-mx_width,wing_inside),
                (-mx_width,-wing_inside),
                (-alps_width,-wing_inside),
                (-alps_width,-wing_outside),
                (-mx_width,-wing_outside),
                (-mx_width,-mx_height),
                (mx_width,-mx_height)
            ]
        elif switch_type == 'mx-open-rotatable':
            points = [
                (mx_width,-mx_height),
                (mx_width,-wing_outside),
                (alps_width,-wing_outside),
                (alps_width,-wing_inside),
                (mx_width,-wing_inside),
                (mx_width,wing_inside),
                (alps_width,wing_inside),
                (alps_width,wing_outside),
                (mx_width,wing_outside),
                (mx_width,mx_height),
                (wing_outside,mx_height),
                (wing_outside,alps_width),
                (wing_inside,alps_width),
                (wing_inside,mx_height),
                (-wing_inside,mx_height),
                (-wing_inside,alps_width),
                (-wing_outside,alps_width),
                (-wing_outside,mx_height),
                (-mx_width,mx_height),
                (-mx_width,wing_outside),
                (-alps_width,wing_outside),
                (-alps_width,wing_inside),
                (-mx_width,wing_inside),
                (-mx_width,-wing_inside),
                (-alps_width,-wing_inside),
                (-alps_width,-wing_outside),
                (-mx_width,-wing_outside),
                (-mx_width,-mx_height),
                (-wing_outside,-mx_height),
                (-wing_outside,-alps_width),
                (-wing_inside,-alps_width),
                (-wing_inside,-mx_height),
                (wing_inside,-mx_height),
                (wing_inside,-alps_width),
                (wing_outside,-alps_width),
                (wing_outside,-mx_height),
                (mx_width,-mx_height)
            ]
        elif switch_type == 'alps':
            points = [
                (alps_width,-alps_height),
                (alps_width,alps_height),
                (-alps_width,alps_height),
                (-alps_width,-alps_height),
                (alps_width,-alps_height),
            ]

        if rotate:
            points = self.rotate_points(points, 90, (0,0))
        if rotate_key:
            points = self.rotate_points(points, rotate_key, (0,0))

        plate = self.center(plate, switch_coord[0], switch_coord[1]).polyline(points).cutThruAll()

        if center_offset > 0:
            # Move back to the center of the key/stabilizer
            plate = plate.center(-center_offset, 0)

        # Cut stabilizers. We have different sections for 2U vs other sizes
        # because cherry 2U stabs are shaped differently from larger stabs.
        # This should be refactored for better readability.
        if layer == 'top':
            # Don't cut stabs on top
            self.x_off += switch_coord[0]
            return plate

        elif (width >= 2 and width < 3) or (rotate and height >= 2 and height < 3):
            # Cut 2 unit stabilizer cutout
            if stab_type == 'cherry-costar':
                points = [
                    (mx_width,-mx_height),
                    (mx_width,-mx_stab_inside_y),
                    (mx_stab_inside_x,-mx_stab_inside_y),
                    (mx_stab_inside_x,-stab_cherry_top_x),
                    (stab_4,-stab_cherry_top_x),
                    (stab_4,-stab_5),
                    (stab_6,-stab_5),
                    (stab_6,-stab_cherry_top_x),
                    (mx_stab_outside_x,-stab_cherry_top_x),
                    (mx_stab_outside_x,-stab_y_wire),
                    (stab_9,-stab_y_wire),
                    (stab_9,stab_cherry_wing_bottom_x),
                    (mx_stab_outside_x,stab_cherry_wing_bottom_x),
                    (mx_stab_outside_x,stab_cherry_bottom_x),
                    (stab_6,stab_cherry_bottom_x),
                    (stab_6,stab_12),
                    (stab_4,stab_12),
                    (stab_4,stab_cherry_bottom_x),
                    (mx_stab_inside_x,stab_cherry_bottom_x),
                    (mx_stab_inside_x,stab_13),
                    (mx_width,stab_13),
                    (mx_width,mx_height),
                    (-mx_width,mx_height),
                    (-mx_width,stab_13),
                    (-mx_stab_inside_x,stab_13),
                    (-mx_stab_inside_x,stab_cherry_bottom_x),
                    (-stab_4,stab_cherry_bottom_x),
                    (-stab_4,stab_12),
                    (-stab_6,stab_12),
                    (-stab_6,stab_cherry_bottom_x),
                    (-mx_stab_outside_x,stab_cherry_bottom_x),
                    (-mx_stab_outside_x,stab_cherry_wing_bottom_x),
                    (-stab_9,stab_cherry_wing_bottom_x),
                    (-stab_9,-stab_y_wire),
                    (-mx_stab_outside_x,-stab_y_wire),
                    (-mx_stab_outside_x,-stab_cherry_top_x),
                    (-stab_6,-stab_cherry_top_x),
                    (-stab_6,-stab_5),
                    (-stab_4,-stab_5),
                    (-stab_4,-stab_cherry_top_x),
                    (-mx_stab_inside_x,-stab_cherry_top_x),
                    (-mx_stab_inside_x,-mx_stab_inside_y),
                    (-mx_width,-mx_stab_inside_y),
                    (-mx_width,-mx_height),
                    (mx_width,-mx_height)
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rotate_stab:
                    points = self.rotate_points(points, rotate_stab, (0,0))
                plate = plate.polyline(points).cutThruAll()
            elif stab_type == 'cherry':
                points = [
                    (mx_stab_inside_x,-mx_stab_inside_y),
                    (mx_stab_inside_x,-stab_cherry_top_x),
                    (mx_stab_outside_x,-stab_cherry_top_x),
                    (mx_stab_outside_x,-stab_y_wire),
                    (stab_9,-stab_y_wire),
                    (stab_9,stab_cherry_wing_bottom_x),
                    (mx_stab_outside_x,stab_cherry_wing_bottom_x),
                    (mx_stab_outside_x,stab_cherry_bottom_x),
                    (stab_6,stab_cherry_bottom_x),
                    (stab_6,stab_cherry_bottom_wing_bottom_y),
                    (stab_4,stab_cherry_bottom_wing_bottom_y),
                    (stab_4,stab_cherry_bottom_x),
                    (mx_stab_inside_x,stab_cherry_bottom_x),
                    (mx_stab_inside_x,stab_13),
                    (-mx_stab_inside_x,stab_13),
                    (-mx_stab_inside_x,stab_cherry_bottom_x),
                    (-stab_4,stab_cherry_bottom_x),
                    (-stab_4,stab_cherry_bottom_wing_bottom_y),
                    (-stab_6,stab_cherry_bottom_wing_bottom_y),
                    (-stab_6,stab_cherry_bottom_x),
                    (-mx_stab_outside_x,stab_cherry_bottom_x),
                    (-mx_stab_outside_x,stab_cherry_wing_bottom_x),
                    (-stab_9,stab_cherry_wing_bottom_x),
                    (-stab_9,-stab_y_wire),
                    (-mx_stab_outside_x,-stab_y_wire),
                    (-mx_stab_outside_x,-stab_cherry_top_x),
                    (-mx_stab_inside_x,-stab_cherry_top_x),
                    (-mx_stab_inside_x,-mx_stab_inside_y),
                    (mx_stab_inside_x,-mx_stab_inside_y),
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rotate_stab:
                    points = self.rotate_points(points, rotate_stab, (0,0))
                plate = plate.polyline(points).cutThruAll()
            elif stab_type == 'costar':
                points_l = [
                    (-stab_4,-stab_5),
                    (-stab_6,-stab_5),
                    (-stab_6,stab_12),
                    (-stab_4,stab_12),
                    (-stab_4,-stab_5)
                ]
                points_r = [
                    (stab_4,-stab_5),
                    (stab_6,-stab_5),
                    (stab_6,stab_12),
                    (stab_4,stab_12),
                    (stab_4,-stab_5)
                ]
                if rotate:
                    points_l = self.rotate_points(points_l, 90, (0,0))
                    points_r = self.rotate_points(points_r, 90, (0,0))
                if rotate_stab:
                    points_l = self.rotate_points(points_l, rotate_stab, (0,0))
                    points_r = self.rotate_points(points_r, rotate_stab, (0,0))
                plate = plate.polyline(points_l).cutThruAll()
                plate = plate.polyline(points_r).cutThruAll()
            elif stab_type in ('alps', 'matias'):
                points_r = [
                    (alps_stab_inside_x, alps_stab_top_y),
                    (alps_stab_ouside_x, alps_stab_top_y),
                    (alps_stab_ouside_x, alps_stab_bottom_y),
                    (alps_stab_inside_x, alps_stab_bottom_y),
                    (alps_stab_inside_x, alps_stab_top_y)
                ]
                points_l = [
                    (-alps_stab_inside_x, alps_stab_top_y),
                    (-alps_stab_ouside_x, alps_stab_top_y),
                    (-alps_stab_ouside_x, alps_stab_bottom_y),
                    (-alps_stab_inside_x, alps_stab_bottom_y),
                    (-alps_stab_inside_x, alps_stab_top_y)
                ]

                if rotate:
                    points_l = self.rotate_points(points_l, 90, (0,0))
                    points_r = self.rotate_points(points_r, 90, (0,0))
                if rotate_stab:
                    points_l = self.rotate_points(points_l, rotate_stab, (0,0))
                    points_r = self.rotate_points(points_r, rotate_stab, (0,0))
                plate = plate.polyline(points_l).cutThruAll()
                plate = plate.polyline(points_r).cutThruAll()
            else:
                log.error('Unknown stab type %s! No stabilizer cut', stab_type)

        # Cut larger stabilizer cutouts
        elif (width >= 3) or (rotate and height >= 3):
            if stab_type == 'cherry-costar':
                points = [
                    (x-stab_cherry_half_width,-stab_y_wire),
                    (x-stab_cherry_half_width,-stab_cherry_top_x),
                    (x-stab_cherry_bottom_wing_half_width,-stab_cherry_top_x),
                    (x-stab_cherry_bottom_wing_half_width,-stab_5),
                    (x+stab_cherry_bottom_wing_half_width,-stab_5),
                    (x+stab_cherry_bottom_wing_half_width,-stab_cherry_top_x),
                    (x+stab_cherry_half_width,-stab_cherry_top_x),
                    (x+stab_cherry_half_width,-stab_y_wire),
                    (x+stab_cherry_outside_x,-stab_y_wire),
                    (x+stab_cherry_outside_x,stab_cherry_wing_bottom_x),
                    (x+stab_cherry_half_width,stab_cherry_wing_bottom_x),
                    (x+stab_cherry_half_width,stab_cherry_bottom_x),
                    (x+stab_cherry_bottom_wing_half_width,stab_cherry_bottom_x),
                    (x+stab_cherry_bottom_wing_half_width,stab_12),
                    (x-stab_cherry_bottom_wing_half_width,stab_12),
                    (x-stab_cherry_bottom_wing_half_width,stab_cherry_bottom_x),
                    (x-stab_cherry_half_width,stab_cherry_bottom_x),
                    (x-stab_cherry_half_width,stab_y_wire),
                    (-x+stab_cherry_half_width,stab_y_wire),
                    (-x+stab_cherry_half_width,stab_cherry_bottom_x),
                    (-x+stab_cherry_bottom_wing_half_width,stab_cherry_bottom_x),
                    (-x+stab_cherry_bottom_wing_half_width,stab_12),
                    (-x-stab_cherry_bottom_wing_half_width,stab_12),
                    (-x-stab_cherry_bottom_wing_half_width,stab_cherry_bottom_x),
                    (-x-stab_cherry_half_width,stab_cherry_bottom_x),
                    (-x-stab_cherry_half_width,stab_cherry_wing_bottom_x),
                    (-x-stab_cherry_outside_x,stab_cherry_wing_bottom_x),
                    (-x-stab_cherry_outside_x,-stab_y_wire),
                    (-x-stab_cherry_half_width,-stab_y_wire),
                    (-x-stab_cherry_half_width,-stab_cherry_top_x),
                    (-x-stab_cherry_bottom_wing_half_width,-stab_cherry_top_x),
                    (-x-stab_cherry_bottom_wing_half_width,-stab_5),
                    (-x+stab_cherry_bottom_wing_half_width,-stab_5),
                    (-x+stab_cherry_bottom_wing_half_width,-stab_cherry_top_x),
                    (-x+stab_cherry_half_width,-stab_cherry_top_x),
                    (-x+stab_cherry_half_width,-stab_y_wire),
                    (x-stab_cherry_half_width,-stab_y_wire)
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rotate_stab:
                    points = self.rotate_points(points, rotate_stab, (0,0))
                plate = plate.polyline(points).cutThruAll()
            elif stab_type == 'cherry':
                points = [
                    (x - stab_cherry_half_width, -stab_y_wire),#1
                    (x - stab_cherry_half_width, -stab_cherry_top_x),#2
                    (x + stab_cherry_half_width, -stab_cherry_top_x),#3
                    (x + stab_cherry_half_width, -stab_y_wire),#4
                    (x + stab_cherry_outside_x, -stab_y_wire),#5
                    (x + stab_cherry_outside_x, stab_cherry_wing_bottom_x),#6
                    (x + stab_cherry_half_width, stab_cherry_wing_bottom_x),#7
                    (x + stab_cherry_half_width, stab_cherry_bottom_x),#8
                    (x + stab_cherry_bottom_wing_half_width, stab_cherry_bottom_x),#9
                    (x + stab_cherry_bottom_wing_half_width, stab_cherry_bottom_wing_bottom_y),#10
                    (x - stab_cherry_bottom_wing_half_width, stab_cherry_bottom_wing_bottom_y),#11
                    (x - stab_cherry_bottom_wing_half_width, stab_cherry_bottom_x),#12
                    (x - stab_cherry_half_width, stab_cherry_bottom_x),#13
                    (x - stab_cherry_half_width, stab_bottom_y_wire),#14
                    (-x + stab_cherry_half_width, stab_bottom_y_wire),#15
                    (-x + stab_cherry_half_width, stab_cherry_bottom_x),#16
                    (-x + stab_cherry_bottom_wing_half_width, stab_cherry_bottom_x),#17
                    (-x + stab_cherry_bottom_wing_half_width, stab_cherry_bottom_wing_bottom_y),#18
                    (-x - stab_cherry_bottom_wing_half_width, stab_cherry_bottom_wing_bottom_y),#19
                    (-x - stab_cherry_bottom_wing_half_width, stab_cherry_bottom_x),#20
                    (-x - stab_cherry_half_width, stab_cherry_bottom_x),#21
                    (-x - stab_cherry_half_width, stab_cherry_wing_bottom_x),#22
                    (-x - stab_cherry_outside_x, stab_cherry_wing_bottom_x),#23
                    (-x - stab_cherry_outside_x, -stab_y_wire),#24
                    (-x - stab_cherry_half_width, -stab_y_wire),#25
                    (-x - stab_cherry_half_width, -stab_cherry_top_x),#26
                    (-x + stab_cherry_half_width, -stab_cherry_top_x),#27
                    (-x + stab_cherry_half_width, -stab_y_wire),#28
                    (x - stab_cherry_half_width, -stab_y_wire),#1
                ]
                if rotate:
                    points = self.rotate_points(points, 90, (0,0))
                if rotate_stab:
                    points = self.rotate_points(points, rotate_stab, (0,0))
                plate = plate.polyline(points).cutThruAll()
            elif stab_type in ('costar', 'matias'):
                points_l = [
                    (-x+stab_cherry_bottom_wing_half_width,-stab_5),
                    (-x-stab_cherry_bottom_wing_half_width,-stab_5),
                    (-x-stab_cherry_bottom_wing_half_width,stab_12),
                    (-x+stab_cherry_bottom_wing_half_width,stab_12),
                    (-x+stab_cherry_bottom_wing_half_width,-stab_5)
                ]
                points_r = [
                    (x-stab_cherry_bottom_wing_half_width,-stab_5),
                    (x+stab_cherry_bottom_wing_half_width,-stab_5),
                    (x+stab_cherry_bottom_wing_half_width,stab_12),
                    (x-stab_cherry_bottom_wing_half_width,stab_12),
                    (x-stab_cherry_bottom_wing_half_width,-stab_5)
                ]
                if rotate:
                    points_l = self.rotate_points(points_l, 90, (0,0))
                    points_r = self.rotate_points(points_r, 90, (0,0))
                if rotate_stab:
                    points_l = self.rotate_points(points_l, rotate_stab, (0,0))
                    points_r = self.rotate_points(points_r, rotate_stab, (0,0))
                plate = plate.polyline(points_l).cutThruAll()
                plate = plate.polyline(points_r).cutThruAll()
            elif stab_type == 'alps':
                # Alps stabilizers
                if width == 6.5:
                    inside_x = alps_stab_inside_x + 31.3
                else:
                    log.error("We don't know how far apart stabs are for alps of %s width!" % width)
                    inside_x = alps_stab_inside_x + 30

                outside_x = inside_x + 2.7 - self.kerf*2
                points_r = [
                    (inside_x, alps_stab_top_y),
                    (outside_x, alps_stab_top_y),
                    (outside_x, alps_stab_bottom_y),
                    (inside_x, alps_stab_bottom_y),
                    (inside_x, alps_stab_top_y)
                ]
                points_l = [
                    (-inside_x, alps_stab_top_y),
                    (-outside_x, alps_stab_top_y),
                    (-outside_x, alps_stab_bottom_y),
                    (-inside_x, alps_stab_bottom_y),
                    (-inside_x, alps_stab_top_y)
                ]

                if rotate:
                    points_l = self.rotate_points(points_l, 90, (0, 0))
                    points_r = self.rotate_points(points_r, 90, (0, 0))
                if rotate_stab:
                    points_l = self.rotate_points(points_l, rotate_stab, (0, 0))
                    points_r = self.rotate_points(points_r, rotate_stab, (0, 0))
                plate = plate.polyline(points_l).cutThruAll()
                plate = plate.polyline(points_r).cutThruAll()
            else:
                log.error('Unknown stab type %s! No stabilizer cut', stab_type)

        self.x_off += switch_coord[0]
        return plate

    def recenter(self, plate):
        """Move back to the centerpoint of the plate
        """
        plate = plate.center(-self.origin[0], -self.origin[1])
        self.origin = (0,0)

        return plate

    def center(self, plate, x, y):
        """Move the center point and record how far we have moved relative to the center of the plate.
        """
        #print 'Moving %s,%s mm. (Origin: %s)' % (x, y, self.origin)
        self.origin = (self.origin[0]+x, self.origin[1]+y)

        return plate.center(x, y)

    def __repr__(self):
        """Print out all KeyboardCase object configuration settings.
        """
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

        return json.dumps(settings, sort_keys=True, indent=4, separators=(',', ': '))

    def export(self, plate, layer):
        """Export the specified layer to the formats specified in self.formats.
        """
        log.info("Exporting %s layer for %s", layer, self.export_basename)
        # draw the part so we can export it
        Part.show(plate.val().wrapped)
        doc = FreeCAD.ActiveDocument
        # export the drawing into different formats
        pwd_len = len(config.app['pwd']) # the absolute part of the working directory (aka - outside the web space)
        self.exports[layer] = []
        if 'js' in self.formats:
            with open("%s/%s_%s.js" % (config.app['export'], layer, self.export_basename), "w") as f:
                cadquery.exporters.exportShape(plate, 'TJS', f)
                self.exports[layer].append({'name': 'js', 'url': '%s/%s_%s.js' % (config.app['export'][pwd_len:], layer, self.export_basename)})
                log.info("Exported 'JS'")
        if 'brp' in self.formats:
            Part.export(doc.Objects, "%s/%s_%s.brp" % (config.app['export'], layer, self.export_basename))
            self.exports[layer].append({'name': 'brp', 'url': '%s/%s_%s.brp' % (config.app['export'][pwd_len:], layer, self.export_basename)})
            log.info("Exported 'BRP'")
        if 'stp' in self.formats:
            Part.export(doc.Objects, "%s/%s_%s.stp" % (config.app['export'], layer, self.export_basename))
            self.exports[layer].append({'name': 'stp', 'url': '%s/%s_%s.stp' % (config.app['export'][pwd_len:], layer, self.export_basename)})
            log.info("Exported 'STP'")
        if 'stl' in self.formats:
            Mesh.export(doc.Objects, "%s/%s_%s.stl" % (config.app['export'], layer, self.export_basename))
            self.exports[layer].append({'name': 'stl', 'url': '%s/%s_%s.stl' % (config.app['export'][pwd_len:], layer, self.export_basename)})
            log.info("Exported 'STL'")
        if 'dxf' in self.formats:
            importDXF.export(doc.Objects, "%s/%s_%s.dxf" % (config.app['export'], layer, self.export_basename))
            self.exports[layer].append({'name': 'dxf', 'url': '%s/%s_%s.dxf' % (config.app['export'][pwd_len:], layer, self.export_basename)})
            log.info("Exported 'DXF'")
        if 'svg' in self.formats:
            importSVG.export(doc.Objects, "%s/%s_%s.svg" % (config.app['export'], layer, self.export_basename))
            self.exports[layer].append({'name': 'svg', 'url': '%s/%s_%s.svg' % (config.app['export'][pwd_len:], layer, self.export_basename)})
            log.info("Exported 'SVG'")
        if 'json' in self.formats and layer == 'switch':
            with open("%s/%s_%s.json" % (config.app['export'], layer, self.export_basename), 'w') as json_file:
                json_file.write(repr(self))
            self.exports[layer].append({'name': 'json', 'url': '%s/%s_%s.json' % (config.app['export'][pwd_len:], layer, self.export_basename)})
            log.info("Exported 'JSON'")

        # remove all the documents from the view before we move on
        for o in doc.Objects:
            doc.removeObject(o.Label)

