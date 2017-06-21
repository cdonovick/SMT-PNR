from util import BiDict

class PNRConfig:
    def __init__(self):
        self._trackconfig = BiDict()

    @property
    def trackconfig(self):
        return self._trackconfig
