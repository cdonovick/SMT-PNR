import sys
major_version = sys.version_info[0]
if major_version > 2:
    from .config import *
from .annotations import *
