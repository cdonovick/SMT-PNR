import io
from contextlib import contextmanager

@contextmanager
def smart_open(file, *pargs, **kwargs):
    if isinstance(file, io.IOBase):
        yield file
    else:
        with open(file, *pargs, **kwargs) as fh:
            yield fh

