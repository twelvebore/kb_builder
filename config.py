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

import os
import sys


pwd = os.path.dirname(__file__)

app = {
    'host': '0.0.0.0',
    'port': 8080,
    'pwd': pwd,
    'static': os.path.join(pwd, 'static'),
    'export': os.path.join(pwd, 'static', 'exports'),
    'formats': ['dxf'],
    'debug': False,
    'log': './kb_builder.log'
}

lib = {
    'freecad_lib_dir': "/usr/lib/freecad/lib",
    'freecad_mod_dir': ""
}


# Setup some environment stuff
if lib.get('freecad_lib_dir'):
    sys.path.append(lib['freecad_lib_dir'])

if lib.get('freecad_mod_dir'):
    for mod in os.listdir(lib['freecad_mod_dir']):
        mod_path = os.path.join(lib['freecad_mod_dir'], mod)
        if os.path.isdir(mod_path): sys.path.append(mod_path)
