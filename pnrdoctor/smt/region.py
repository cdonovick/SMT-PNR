
from pnrdoctor.util import Constant, NamedObject, NamedIDObject, FlyWeightMeta

class _SYMBOLIC(Constant):
    __slots__ = ()

SYMBOLIC = _SYMBOLIC()


_NO_VAL = frozenset((None, SYMBOLIC))
def _is_set(*vals): return all(v not in _NO_VAL for v in vals)


class Region(NamedIDObject):
    @classmethod
    def from_frabic(cls, name, fabric):
        rows = Scalar('rows', fabric.rows)
        cols = Scalar('cols', fabric.cols)
        tracks = Category('tracks', fabric.num_tracks)

        return cls(name, (rows, cols, tracks))


    def __init__(self,
            name,
            space,
            from_space=False,
            sizes={},
            positions={},
            categories={},
            subregions=(),
            ):
        '''
        space : [Category | Scalar]
        sizes : {Scalar : int | None | SYMBOLIC}
        positions : {Scalar : int | None | SYMBOLIC}
        categories : {Category : int | None | SYMBOLIC}
        subregions : [Region]
        '''

        space = frozenset(space)
        scalar_space = frozenset(filter(lambda x : isinstance(x, Scalar), space))
        category_space = frozenset(filter(lambda x : isinstance(x, Category), space))

        # basic sanity checks
        if from_space:
            assert not sizes
            assert not positions
            assert not categories


        assert all(isinstance(d, Dimension) for d in space)
        assert space == scalar_space | category_space
        assert sizes.keys() <= scalar_space
        assert positions.keys() <= scalar_space
        assert categories.keys() <= category_space

        for r in subregions:
            assert r.space <= space

        # set up empty object
        super().__init__(name)

        self._parent = None
        self._space = frozenset()
        self._scalar_space = frozenset()
        self._category_space = frozenset()

        self._positions = dict()
        self._sizes = dict()
        self._categories = dict()

        if from_space:
            for d in scalar_space:
                size[d] = d.size
            for d in category_space:
                self

        # init
        self._extend_space(space)
        self.set_position(positions)
        self.set_size(sizes)
        self.add_subregions(*subregions)

    @property
    def categories(self):
        return self._categories

    @property
    def parent(self):
        return self._parent

    @property
    def positions(self):
        return self._positions

    @property
    def sizes(self):
        return self._sizes

    @property
    def space(self):
        return self._space

    @property
    def subregions(self):
        return self._subregions

    def _clone(self):
        return type(self)(
            self.name,
            self.space,
            sizes=self.sizes,
            positions=self.positions,
            categories=self.categories,
            subregions=(r._clone() for r in self.subregions)
        )

    def _extend_space(self, space):
        space = frozenset(space)
        for d in space:
            assert isinstance(d, Dimension), d

        space = space | self.space
        scalar_space = frozenset(filter(lambda x : isinstance(x, Scalar), space))
        category_space = frozenset(filter(lambda x : isinstance(x, Category), space))

        assert space == scalar_space | category_space

        # default everything to None
        for d in scalar_space - self._scalar_space:
            self._positions[d] = None
            self._sizes[d] = None

        for d in category_space - self._category_space:
            self._categories[d] = None

        self._space = space
        self._scalar_space = scalar_space
        self._category_space = category_space

    def add_subregions(self, *subregions):
        for r in subregions:
            assert r.space <= self.space
            assert r.parent is None
            for d in r._scalar_space:
                if not _is_set(self.sizes[d]):
                    continue

                if _is_set(r.positions[d]):
                    assert r.position[d] < self.sizes[d]
                if _is_set(r.sizes[d]):
                    assert r.sizes[d] <= self.sizes[d]
                if _is_set(r.positions[d], r.sizes[d]):
                    assert r.positions[d] + r.sizes[d] <= self.sizes[d]

            for d in r._category_space:
                if _is_set(self.categories[d], r.categories[d]):
                    assert ~self.categories[d] & r.categories[d] == 0
            r._extend_space(self.space)
            r._parent = self

    def set_category(self, **categories):
        for d,c in categories.items():
            assert d in self._category_space
            if _is_set(c):
                if self.parent is None:
                    assert c & ~d.mask == 0
                elif _is_set(self.parent.categories[d]):
                    assert c & ~self.parent.categories[d] == e

            self.categories[d] = c

    def set_position(self, positions):
        for d,p in positions.items():
            # assert stuff
            assert d in self._scalar_space
            if _is_set(p):
                s = self.sizes[d]
                if self.parent is None:
                    assert p < d.size
                    if _is_set(s):
                        assert s + p <= d.size

                elif _is_set(self.parent.sizes[d]):
                    assert p < self.parent.sizes[d]
                    if _is_set(s):
                        assert s + p <= self.parent.sizes[d]

            # set position
            self.positions[d] = p


    def set_size(self, sizes):
        for d,s in sizes.items():
            # assert stuff
            assert d in self._scalar_space
            if _is_set(s):
                p = self.positions[d]
                if self.parent is None:
                    assert s <= d.size
                    if _is_set(p):
                        assert s + p <= d.size

                elif _is_set(self.parent.sizes[d]):
                    assert s <= self.parent.sizes[d]
                    if _is_set(p):
                        assert s + p <= self.parent.sizes[d]

            # set size
            self.sizes[d] = s


class Dimension(NamedIDObject, metaclass=FlyWeightMeta):
    def __init__(self, name):
        super().__init__(name)

class Scalar(Dimension):
    def __init__(self, name, size):
        super().__init__(name)
        self._size = size

    @property
    def size(self):
        return self._size

class Category(Dimension):
    def __init__(self, name, n_categories):
        super().__init__(name)
        self._mask = 2**n_categories - 1

    @property
    def mask(self):
        return self._mask

