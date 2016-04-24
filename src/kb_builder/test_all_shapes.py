"""Test the basic functionality with a simple plate including every switch type.
"""
import filecmp
import hjson
from builder import KeyboardCase

def test_all_shapes():
    layout = '{"layout": [' + open("test_all_shapes.kle").read() + ']}'
    layout = hjson.loads(layout)['layout']
    case = KeyboardCase(layout, ['dxf'])
    case.create_switch_layer('switch')
    case.export('switch', 'test_exports')

    # Basic checks
    assert case.name == 'e85e91426fc387b23477c7a5cc17bca39f093c8f'
    assert case.formats == ['dxf']
    assert case.kerf == 0
    assert case.layers == {'switch': {}}
    assert case.width == 247.65
    assert case.height == 95.25
    assert case.inside_width == 247.65
    assert case.inside_height == 95.25

    # Make sure the DXF matches the reference DXF
    assert filecmp.cmp('test_exports/switch_%s.dxf' % case.name, 'test_exports/switch_%s.dxf.knowngood' % case.name) == True

    return True
