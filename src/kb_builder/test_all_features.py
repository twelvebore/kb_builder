"""Test the basic functionality with a simple plate including every switch type.
"""
import filecmp
import hjson
from builder import KeyboardCase

def test_all_features():
    layout = '{"layout": [' + open("test_all_features.kle").read() + ']}'
    layout = hjson.loads(layout)['layout']
    case = KeyboardCase(layout, ['dxf'])

    print case.layers
    case.create_bottom_layer('bottom')
    case.export('bottom', 'test_exports')

    case.create_closed_layer('closed')
    case.export('closed', 'test_exports')

    case.create_open_layer('open')
    case.export('open', 'test_exports')

    case.create_switch_layer('reinforcing')
    case.export('reinforcing', 'test_exports')

    case.create_switch_layer('switch')
    case.export('switch', 'test_exports')

    case.create_switch_layer('top')
    case.export('top', 'test_exports')

    assert case.name == 'test_all_features'
    assert case.formats == ['dxf']
    assert case.kerf == 0.1
    assert case.width == 259.65
    assert case.height == 107.25
    assert case.inside_width == 251.45
    assert case.inside_height == 99.05

    for layer in ('bottom', 'closed', 'open', 'reinforcing', 'switch', 'top'):
        assert layer in case.layers
        assert filecmp.cmp('test_exports/switch_%s.dxf' % case.name, 'test_exports/switch_%s.dxf.knowngood' % case.name) == True

    return True
