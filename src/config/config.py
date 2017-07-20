from collections import namedtuple
from .annotations import Annotations
import pnr


class ConfigEngine:
    def __init__(self):
        self._config = dict()
        self._state_loaded = False
        self._fabric = None

    @property
    def config(self):
        return self._config

    @property
    def fabric(self):
        return self._fabric

    @fabric.setter
    def fabric(self, fab):
        self._fabric = fab

    def __setitem__(self, k, v):
        self._config[k] = v

    def __getitem__(self, k):
        return self._config[k]

    def load_state(self, p_state, r_state):
        self._p_state = p_state
        self._r_state = r_state
        self._state_loaded = True

    def write_bitstream(self, filename, annotate=True):
        if not self._state_loaded:
            raise RuntimeError('Need to load state before writing bitstream')

        pnr.write_bitstream(self._fabric, filename, self, annotate, self._p_state,
                            self._r_state, Annotations())


configindex = namedtuple('configindex', 'ps resource')


class config:
    def __init__(self, d=None, **kwargs):
        if d:
            for k, v in d.items():
                setattr(self, k, v)

        for k, v in kwargs.items():
            setattr(self, k, v)

    def __getitem__(self, k):
        return getattr(self, k)
