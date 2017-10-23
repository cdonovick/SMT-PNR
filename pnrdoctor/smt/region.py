
from pnrdoctor.util import Constant, NamedObject, NamedIDObject, FlyWeightMeta

class _SYMBOLIC(Constant):
    __slots__ = ()

SYMBOLIC = _SYMBOLIC()


_NO_VAL = frozenset((None, SYMBOLIC))
def _is_set(*vals): return all(v not in _NO_VAL for v in vals)


class Region(NamedIDObject):
    @classmethod
    def from_frabic(cls, name, fabric):
        return cls(name, (fabric.rows_dim, fabric.cols_dim, fabric.tracks_dim, fabric.layers_dim), from_space=True)


    def __init__(self,
            name,
            space,
            from_space=False,
            size={},
            position={},
            category={},
            subregions=(),
            ):
        '''
        space : [Category | Scalar]
        size : {Scalar : int | None | SYMBOLIC}
        position : {Scalar : int | None | SYMBOLIC}
        category : {Category : int | None | SYMBOLIC}
        subregions : [Region]
        '''

        space = frozenset(space)
        scalar_space = frozenset(filter(lambda x : isinstance(x, Scalar), space))
        category_space = frozenset(filter(lambda x : isinstance(x, Category), space))

        # basic sanity checks
        if from_space:
            assert not size
            assert not position
            assert not category


        assert all(isinstance(d, Dimension) for d in space)
        assert space == scalar_space | category_space
        assert size.keys() <= scalar_space
        assert position.keys() <= scalar_space
        assert category.keys() <= category_space

        for r in subregions:
            assert r.space <= space

        # set up empty object
        super().__init__(name)

        self._parent = None
        self._space = frozenset()
        self._scalar_space = frozenset()
        self._category_space = frozenset()

        self._position = dict()
        self._size = dict()
        self._category = dict()

        if from_space:
            for d in scalar_space:
                self.size[d] = d.size


        # init
        self._extend_space(space)
        self.set_category(category)
        self.set_position(position)
        self.set_size(size)
        self.add_subregions(*subregions)

    @property
    def category(self):
        return self._category

    @property
    def parent(self):
        return self._parent

    @property
    def position(self):
        return self._position

    @property
    def size(self):
        return self._size

    @property
    def space(self):
        return self._space

    @property
    def subregions(self):
        return self._subregions

    def set_category(self, category):
        for d,c in category.items():
            # assert stuff
            assert d in self._category_space
            if _is_set(c):
                if self.parent is None:
                    assert c & ~d.mask == 0
                elif _is_set(self.parent.category[d]):
                    assert c & ~self.parent.category[d] == e

            self.category[d] = c

    def set_position(self, position):
        for d,p in position.items():
            # assert stuff
            assert d in self._scalar_space
            if _is_set(p):
                s = self.size[d]
                if self.parent is None:
                    assert p < d.size
                    if _is_set(s):
                        assert s + p <= d.size

                elif _is_set(self.parent.size[d]):
                    assert p < self.parent.size[d]
                    if _is_set(s):
                        assert s + p <= self.parent.size[d]

            # set position
            self.position[d] = p


    def set_size(self, size):
        for d,s in size.items():
            # assert stuff
            assert d in self._scalar_space
            if _is_set(s):
                p = self.position[d]
                if self.parent is None:
                    assert s <= d.size
                    if _is_set(p):
                        assert s + p <= d.size

                elif _is_set(self.parent.size[d]):
                    assert s <= self.parent.size[d]
                    if _is_set(p):
                        assert s + p <= self.parent.size[d]

            # set size
            self.size[d] = s

    def add_subregions(self, *subregions):
        for r in subregions:
            assert r.space <= self.space
            assert r.parent is None
            for d in r._scalar_space:
                if not _is_set(self.size[d]):
                    continue

                if _is_set(r.position[d]):
                    assert r.position[d] < self.size[d]
                if _is_set(r.size[d]):
                    assert r.size[d] <= self.size[d]
                if _is_set(r.position[d], r.size[d]):
                    assert r.position[d] + r.size[d] <= self.size[d]

            for d in r._category_space:
                if _is_set(self.category[d], r.category[d]):
                    assert ~self.category[d] & r.category[d] == 0
            r._extend_space(self.space)
            r._parent = self

    def make_subregion(self, name):
        r = type(self)(name=name, space=(), from_space=True)

        self.add_subregions(r)
        return r

    @property
    def is_static(self):
        for x in (self.size, self.position, self.category):
            for v in x.values():
                if v is SYMBOLIC:
                    return False
        return True

    def _clone(self):
        return type(self)(
            self.name,
            self.space,
            size=self.size,
            position=self.position,
            category=self.category,
            subregions=self.subregions,
        )

    def _deep_clone(self):
        return type(self)(
            self.name,
            self.space,
            size=self.size,
            position=self.position,
            category=self.category,
            subregions=(r._deep_clone() for r in self.subregions),
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
            self._position[d] = None
            self._size[d] = None

        for d in category_space - self._category_space:
            self._category[d] = None

        self._space = space
        self._scalar_space = scalar_space
        self._category_space = category_space

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
    def __init__(self, name, n_categories, one_hot=False):
        super().__init__(name)
        self._size = n_categories
        self._mask = 2**n_categories - 1
        self._one_hot = one_hot

    @property
    def mask(self):
        return self._mask

    @property
    def size(self):
        return self._size

    @property
    def is_one_hot(self):
        return self._one_hot
