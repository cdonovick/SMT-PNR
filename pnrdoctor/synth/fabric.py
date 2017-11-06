from pnrdoctor.smt.region import Scalar, Region, Category

class Fabric:
    def __init__(self, max_x, max_y, max_z):
        self._max_x = max_x
        self._max_y = max_y
        self._max_z = max_z


        self._x_dim = xd = Scalar('x', self.max_x)
        self._y_dim = yd = Scalar('y', self.max_y)
        self._z_dim = zd = Category('z', self.max_z)

        self._dims = { 
            'x' : xd,
            'y' : yd,
            'z' : zd,
        }

        self._bounds = {
            'x' : max_x,
            'y' : max_y,
            'z' : max_z,
        }

        self._region = Region('Fabric', self.dims.values(), from_space=True)

    @property
    def max_x(self):
        return self._max_x

    @property
    def max_y(self):
        return self._max_y

    @property
    def max_z(self):
        return self._max_z

    @property
    def bounds(self):
        return self._bounds

    @property
    def x_dim(self):
        return self._x_dim

    @property
    def y_dim(self):
        return self._y_dim

    @property
    def z_dim(self):
        return self._z_dim

    @property
    def dims(self):
        return self._dims

    @property
    def region(self):
        return self._region
