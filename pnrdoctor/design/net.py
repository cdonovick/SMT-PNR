from pnrdoctor.util import IDObject

class Tie(IDObject):
    def __init__(self, src, src_port, dst, dst_port, width=1):
        IDObject.__init__(self)

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


class Net(IDObject):
    '''
       Holds a collection of ties that make up a net.
    '''
    def __init__(self, ties=None):
        IDObject.__init__(self)
        if not isinstance(ties, set):
            self._ties = set()
            self._width = None
        else:
            self._ties = ties
            self._width = next(iter(ties)).width
            for tie in ties:
                assert tie.width == self._width, \
                  'Expecting net to contain ties of the same width'
                tie.net = self
                for rtie in tie.regs:
                    rtie.net = self


    def add_tie(self, tie):
        self._ties.add(tie)
        if self._width is None:
            self._width = tie.width
        else:
            assert tie.width == self._width, \
              'Cannot add tie of different width'
        tie.net = self

    def remove_tie(self, tie):
        self._ties.remove(tie)
        tie.net = None

    @property
    def ties(self):
        return self._ties

    @property
    def width(self):
        return self._width

    def __repr__(self):
        tie_strs = ''
        for tie in self._ties:
            tie_strs += tie.__repr__() + ', '

        tie_strs = tie_strs[:-2]

        return 'Net: <{}>'.format(tie_strs)
