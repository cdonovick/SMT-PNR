from util import IDObject

class Net(IDObject):
    def __init__(self, src, src_port, dst, dst_port, width=1):
        super().__init__()
        self._src = src
        self._dst = dst
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
    def width(self):
        return self._width

    def __repr__(self):
        return '{} -[{}]-> {}'.format(self.src.name, self.width, self.dst.name)


