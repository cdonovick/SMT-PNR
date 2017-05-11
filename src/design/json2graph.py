import json
from . import module

def load_json(fname):
    modules = []
    nets = []

    with open(fname, 'r') as f: 
        json_dict = json.load(f)

    for mdict in json_dict['modules']:
        modules.append(module.PcbModule(name   = mdict['reference'],
                                        width  = mdict['width'],
                                        height = mdict['height'],
                                        x      = mdict['x'],
                                        y      = mdict['y'],
                                        theta  = mdict['theta'],
                                        mirror = mdict['mirror'],
                                        pinned = mdict['fixed']))
       
    return modules, nets
