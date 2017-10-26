from enum import Enum, auto
from pnrdoctor.smt.region import Scalar, Region, Category
class Fabric:
    def __init__(self, max_x, max_y, kind_map, kind_cap):
        self._max_x = max_x
        self._max_y = max_y
        self._locations = kind_map
        self._kind_cap = kind_cap


        self._x_dim = xd = Scalar('x', self.max_x)
        self._y_dim = yd = Scalar('y', self.max_y)
        self._dims = dict()
        self._bounds = dict()
        for k, z in kind_cap.items():
            self._bounds[k] = z
            self._dims[k] = kd = Scalar(k, z)
            #self._dims[k] = kd = Category(k, z, one_hot=True)

        assert 'x' not in self.dims
        assert 'y' not in self.dims
        self.dims['x'] = xd
        self.dims['y'] = yd
        self.bounds['x'] = max_x
        self.bounds['y'] = max_y

        self._region = Region('FPGA', self.dims.values(), from_space=True)



    @property
    def max_x(self):
        return self._max_x

    @property
    def max_y(self):
        return self._max_y

    @property
    def bounds(self):
        return self._bounds

    @property
    def locations(self):
        return self._locations

    @property
    def region(self):
        return self._region

    @property
    def x_dim(self):
        return self._x_dim

    @property
    def y_dim(self):
        return self._y_dim

    @property
    def dims(self):
        return self._dims
