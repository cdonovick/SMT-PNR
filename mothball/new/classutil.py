import itertools as it

_object_id = it.count().__next__

class IDObject:
    def __init__(self):
        self._id = _object_id()

    def __eq__(self, other):
        return isinstance(other, type(self)) and self._id == other._id

    def __ne__(self, other):
        return not isinstance(other, type(self)) or not self._id == other._id

    def __hash__(self):
        return hash(self._id)


    @property
    def id(self):
        return self._id

class NamedIDObject(IDObject):
    def __init__(self, name):
        super().__init__()
        self._name = '{}_{}'.format(name, self.id)

    @property
    def name(self):
        return self._name

class ValidContainer:
    '''wrapper class that allows data to marked invalid '''
    __slots__ = '_data', '_valid'

    def __init__(self):
        self.mark_invalid()

    def mark_invalid(self):
        self._valid = False

    @property
    def valid(self):
        return self._valid

    @property
    def data(self):
        if not self.valid:
            raise AttributeError('Data is invalid')
        return self._data

    @data.setter
    def data(self, data):
        self._valid = True
        self._data = data

    def __repr__(self):
        if self.valid:
            return repr(data)
        else:
            return 'Invalid'

