from pnrdoctor.util import IDObject, NamedIDObject

class Tie(IDObject):
    def __init__(self, src, src_port, dst, dst_port, width=1):
        super().__init__()

        self._src = src
        self._dst = dst
        self._src_port = src_port
        self._dst_port = dst_port
        src._add_output(self, src_port)
        dst._add_input(self, dst_port)
        self._width = width

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    @property
    def src_port(self):
        return self._src_port

    @property
    def dst_port(self):
        return self._dst_port

    @property
    def width(self):
        return self._width

    def __repr__(self):
        return '{}:{} -[{}]-> {}:{}'.format(self.src.name,self.src.id, self.width, self.dst.name, self.dst.id)


class Net(NamedIDObject):
    '''
       Holds a collection of ties that make up a net.
    '''
    def __init__(self, name='', ties=set()):
        super().__init__(name)
        self._ties=frozenset(ties)
        terms = set()
        w = None
        for t in self.ties:
            if w is None:
                w = t.width
            else:
                assert t.width == w
            terms.add(t.src)
            terms.add(t.dst)

        self._terminals = frozenset(terms)


    @property
    def ties(self):
        return self._ties

    @property
    def width(self):
        return self._width

    @property
    def terminals(self):
        return self._terminals
