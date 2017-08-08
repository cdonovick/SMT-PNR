import io
from contextlib import contextmanager

@contextmanager
def smart_open(file, *pargs, **kwargs):
    try:
        if isinstance(file, io.IOBase):
            fh = file
            close = False
        else:
            fh = open(file, *pargs, **kwargs)
            close = True

        yield fh
    finally:
        if close:
            fh.close()

