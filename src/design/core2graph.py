import coreir

def load_core(file):
    mods = dict()
    ops = dict()

    c = coreir.Context()
    m = c.load_from_file(file)
    d = m.get_definition()
    l = d.get_instances()
    for i in l:
        s = i.select('out')
        a = s.get_ancestors()
        mods[(a[0], a[1])] = []
        ws = s.get_connected_wireables()
        ops[(a[0])] = 'add'
        for w in ws:
            aw = w.get_ancestors()
            if aw[1] == 'in0':
                mods[(a[0], a[1])].append((aw[0], 'a', 16))
            elif aw[1] == 'in1':
                mods[(a[0], a[1])].append((aw[0], 'b', 16))

    return mods, ops
