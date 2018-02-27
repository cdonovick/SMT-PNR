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
        try:
            return self._config[k]
        except KeyError:
            raise KeyError("Missing IO info for: {}".format(k))

    def load_state(self, p_state, r_state):
        self._p_state = p_state
        self._r_state = r_state
        self._state_loaded = True

    @property
    def p_state(self):
        return self._p_state

    @property
    def r_state(self):
        return self._r_state


class config:
    def __init__(self, d=None, **kwargs):
        if d:
            for k, v in d.items():
                setattr(self, k, v)

        for k, v in kwargs.items():
            setattr(self, k, v)

    def __getitem__(self, k):
        return getattr(self, k)
