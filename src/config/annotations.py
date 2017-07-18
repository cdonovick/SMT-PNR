class Annotations:
    '''
       Class to hold the annotation formats
       To be used at multiple levels in tool flow for
       comparison purposes
    '''

    def connect_wire(self, wire_num, src_name, snk_name, row=None, col=None):
        s = 'connect wire {} ({}) to {}'.format(wire_num, src_name, snk_name)

        return self.__check_tile(row, col, s)

    def latch_wire(self, wire_num, src_name, snk_name, row=None, col=None):
        s = 'latch wire {} ({}) before connecting to {}'.format(wire_num, src_name, snk_name)

        return self.__check_tile(row, col, s)

    # use same one for wire and const
    def load_reg(self, reg_name, const=None, row=None, col=None):
        s = 'load `{}` reg with '.format(reg_name)

        if const:
            s = s + 'const: {}'.format(const)
        else:
            s = s + 'wire'

        return self.__check_tile(row, col, s)

    # use same for actual ops, input and output...
    def op_config(self, op_name, value):
        return '{} = {}'.format(op_name, value)

    def read_from(self, _type, name):
        assert _type in {'reg', 'wire'}
        return 'read from {} `{}`'.format(_type, name)

    def format_comment(self, comment):
        s = []
        for bit, c in comment.items():
            s.append('# data[{}] : {}\n'.format(bit, c))

        return ''.join(s)

    def __check_tile(self, row, col, s):
        if row is not None and col is not None:
            return '@ tile ({}, {}) {}'.format(row, col, s)
        else:
            return s


