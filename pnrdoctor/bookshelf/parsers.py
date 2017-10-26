from pnrdoctor.util import BiMultiDict
import os

import sys
import functools as ft

def parse_all(aux):
    files = parse_aux(aux)

    lib_f = None
    nets_f = None
    nodes_f = None
    pl_f = None
    scl_f = None
    wts_f = None


    for f in files:
        if f.endswith('.lib'):
            assert lib_f is None
            lib_f = f
        elif f.endswith('.nodes'):
            assert nodes_f is None
            nodes_f = f
        elif f.endswith('.nets'):
            assert nets_f is None
            nets_f = f
        elif f.endswith('.pl'):
            assert pl_f is None
            pl_f = f
        elif f.endswith('.scl'):
            assert scl_f is None
            scl_f = f
        elif f.endswith('.wts'):
            assert wts_f is None
            wts_f = f
        else:
            raise ValueError('Unknown filetype: {}'.format(f))

    assert lib_f is not None
    assert nets_f is not None
    assert nodes_f is not None
    assert pl_f is not None
    assert scl_f is not None
    assert wts_f is not None

    site_types, site_kinds, kinds, site_map, max_x, max_y = parse_scl(scl_f)
    # site_types :: site_name -> kind -> capacity
    # site_kinds :: site_name <-> kind
    # kinds      :: kind <-> resource
    # site_map   :: site_name <-> (x, y)

    instances = parse_nodes(nodes_f)
    # instances :: instance_name <-> resource

    placement = parse_pl(pl_f)
    # placement :: instance_name <-> (x, y, z)

    cells = parse_lib(lib_f)
    # cells :: resource -> port_name -> ((INPUT | OUTPUT), (CLOCK | CTRL | SIG))

    nets = parse_nets(nets_f)
    # nets :: net_name -> {(instance_name, port_name)}

    # ASSERT SANITY

    assert site_map.keys() <= site_types.keys()
    assert site_kinds.keys() == site_types.keys()
    # site_name[*].values() == site_kinds.values()
    assert set.union(*map(set, site_types.values())) == site_kinds.values()
    assert site_kinds.values() == kinds.keys()



    assert instances.values() <= kinds.values()
    assert kinds.values() == cells.keys()
    assert placement.keys() <= instances.keys()

    for (x,y) in site_map.I:
        assert len(site_map.I[(x,y)]) == 1
        assert x < max_x
        assert y < max_y

    for inst, (x,y,z) in placement.items():
        c_res = instances[inst]
        assert len(c_res) == 1
        res_l = kinds.I[c_res[0]]

        # the sites that could potentially hold this inst
        p_sites = ft.reduce(set.union, (site_kinds[r] for r in res_l))

        # the site at (x,y)
        site_name = site_map.I[(x,y)][0]

        # the inst can be placed here
        assert site_name in p_sites
        # the inst has valid z
        assert any(z < site_types[site_name][r] for r in res_l if r in site_types[site_name])

    for terminal_set in nets.values():
        num_drivers = 0
        for (inst, port) in terminal_set:
            assert inst in instances
            assert port in cells[instances[inst][0]]
            if cells[instances[inst][0]][port][0] == 'OUTPUT':
                num_drivers += 1
        assert num_drivers == 1, terminal_set

    for res in instances.I:
        t = False
        for kind in kinds.I[res]:
            for site_name in site_kinds.I[kind]:
                t = len(site_map[site_name]) > 0
                if t:
                    break
            if t:
                break
        # assert for all resources in the design there is a spot to put them
        assert t

    # END SANITY CHECKS

    # Strip info we don't care about, e.g., sites

    kind_map = BiMultiDict()
    # kind <-> (x, y)
    kind_cap = dict()
    # kind -> max_z
    for site_name, d_kind_cap in site_types.items():
        for kind, max_z in d_kind_cap.items():
            if kind in kind_cap:
                # -- HACK --
                # assume max_z is the same for all (x,y)
                # if this assumption is wrong constraint building is going to be rough
                # this is equivalent to assuming each kind exists in only one site
                assert kind_cap[kind] == max_z
            else:
                kind_cap[kind] = max_z

            for (x, y) in site_map[site_name]:
                kind_map[kind] = (x, y)

    modules = dict()
    # inst_name -> (kind, resource, ports)
    for inst, res in instances.items():
        assert inst not in modules
        # -- HACK --
        # if more than one kind can hold resource constraint building is gunna be rough
        assert len(kinds.I[res]) == 1
        modules[inst] = {
                'kind'  :  kinds.I[res][0],
                'res'   :  res,
                'ports' :  cells[res]
        }

    return kind_map, kind_cap, modules, nets, placement, max_x, max_y



def parse_aux(aux):
    done = False
    prefix = os.path.dirname(os.path.join(os.getcwd(), aux))
    with open(aux, 'r') as file:
        for line in file:
            line=line.strip()
            if not line:
                continue
            if line[0] == '#':
                continue
            assert not done
            words = line.split()
            assert words[0] == 'design'
            assert words[1] == ':'

            files = words[2:]
            done  = True

    return map(lambda f : os.path.join(prefix, f), files)

def parse_lib(lib):
    with open(lib, 'r') as file:
        res = None
        # resource -> port_name -> ((INPUT | OUTPUT), (CLOCK | CTRL | SIG))
        cells = dict()
        for line in file:
            line = line.strip()
            #blank line
            if not line:
                continue

            words = line.split()
            if not res:
                assert len(words) == 2
                assert words[0] == 'CELL'
                res = words[1]
                cells[res] = dict()
            elif words[0] == 'END':
                assert len(words) == 2
                assert words[1] == 'CELL'
                res = None
            else:
                assert len(words) == 3 or len(words) == 4
                assert words[0] == 'PIN'
                words.append('SIG')
                p = words[1]
                p_dir = words[2]
                p_type = words[3]
                assert p_dir in ('INPUT', 'OUTPUT')
                assert p_type in ('CLOCK', 'CTRL', 'SIG'), p_type
                cells[res][p] = (p_dir, p_type)
    return cells


def parse_nodes(nodes):
    with open(nodes, 'r') as file:
        # instance_name <-> resource
        insts = BiMultiDict()
        for line in file:
            line = line.strip()
            #blank line
            if not line:
                continue

            words = line.split()
            assert len(words) == 2
            inst = words[0]
            res = words[1]
            insts[inst] = res
    return insts


def parse_nets(nets):
    with open(nets, 'r') as file:
        net = None
        # net_name -> {(instance, port)}
        nets = dict()
        for line in file:
            line = line.strip()
            #blank line
            if not line:
                continue
            words = line.split()

            if not net:
                assert len(words) == 3
                assert words[0] == 'net'
                net = words[1]
                assert net not in nets
                n_degree = int(words[2])
                nets[net] = set()
            else:
                if words[0] == 'endnet':
                    assert len(words) == 1
                    assert len(nets[net]) == n_degree
                    net = None
                else:
                    assert len(words) == 2
                    inst = words[0]
                    port = words[1]
                    nets[net].add((inst, port))
    return nets


def parse_pl(pl):
    with open(pl, 'r') as file:
        #instance_name -> (x, y, z)
        placement = BiMultiDict()
        for line in file:
            line = line.strip()
            #blank line
            if not line:
                continue

            words = line.split()
            assert len(words) == 4 or len(words) == 5
            inst = words[0]
            x = int(words[1])
            y = int(words[2])
            z = int(words[3])
            placement[inst] = (x,y,z)

    return placement


def parse_scl(scl):
    with open(scl, 'r') as file:
        in_site = False
        site_name = None
        # site_name -> kind -> capacity
        site_types = dict()
        # site_name <-> kind
        site_kinds = BiMultiDict()

        in_resources = False
        # kind <-> resource
        kinds = BiMultiDict()


        in_map = False
        max_x = 0
        max_y = 0
        # site_name <-> (x, y)
        site_map = BiMultiDict()

        for line in file:
            line = line.strip()
            #blank line
            if not line:
                continue

            words = line.split()
            #stateless
            if not any((in_site, in_resources, in_map)):
                if words[0] == 'SITE':
                    assert len(words) == 2
                    in_site = True
                    site_name = words[1]
                    site_types[site_name] = dict()
                elif words[0] == 'RESOURCES':
                    assert len(words) == 1
                    in_resources = True
                elif words[0] == 'SITEMAP':
                    assert len(words) == 3
                    max_x = int(words[1])
                    max_y = int(words[2])
                    in_map = True
                else:
                    raise ValueError("Can't handle block line: {}".format(line))
            # SITE
            elif in_site:
                assert not in_resources
                assert not in_map
                assert site_name
                if words[0] == 'END':
                    assert len(words) == 2
                    assert words[1] == 'SITE'
                    site_name = None
                    in_site=False
                else:
                    assert len(words) == 2
                    res = words[0]
                    n = int(words[1])
                    site_types[site_name][res] = n
                    site_kinds[site_name] = res
            # RESOURCES
            elif in_resources:
                assert not in_map
                assert not site_name
                if words[0] == 'END':
                    assert len(words) == 2
                    assert words[1] == 'RESOURCES'
                    in_resources = False
                else:
                    assert len(words) >= 2
                    res = words[0]
                    for r in words[1:]:
                        kinds[res] = r
            # SITEMAP
            else:
                assert in_map
                assert not site_name
                if words[0] == 'END':
                    assert len(words) == 2
                    assert words[1] == 'SITEMAP'
                    in_resources = False
                else:
                    assert len(words) == 3
                    x = int(words[0])
                    y = int(words[1])
                    site_type = words[2]
                    site_map[site_type] = (x,y)

    return site_types, site_kinds, kinds, site_map, max_x, max_y

def parse_wts(wts):
    pass

