from util import class_property

class Annotations:
    '''
       Class to hold the annotation formats
       To be used at multiple levels in tool flow for
       comparison purposes
    '''

    @class_property
    def connect_wire_str(cls):
        return 'connect wire {} ({}) to {}'

    @classmethod
    def connect_wire(cls, wire_num, src_name, snk_name, row=None, col=None):
        s = cls.connect_wire_str.format(wire_num, src_name, snk_name)

        return cls.__check_tile(row, col, s)

    @class_property
    def latch_wire_str(cls):
        return 'latch wire {} ({}) before connecting to {}'

    @classmethod
    def latch_wire(cls, wire_num, src_name, snk_name, row=None, col=None):
        s = cls.latch_wire_str.format(wire_num, src_name, snk_name)

        return cls.__check_tile(row, col, s)

    @class_property
    def load_reg_str(cls):
        return 'load `{}` reg with '

    # use same one for wire and const
    @classmethod
    def load_reg(cls, reg_name, const=None, row=None, col=None):
        s = cls.load_reg_str.format(reg_name)

        if const is not None:
            s = s + 'const: {}'.format(const)
        else:
            s = s + 'wire'

        return cls.__check_tile(row, col, s)

    @class_property
    def op_config_str(cls):
        return '{} = {}'

    # use same for actual ops, input and output...
    @classmethod
    def op_config(cls, op_name, value):
        return cls.op_config_str.format(op_name, value)

    @class_property
    def read_from_str(cls):
        return 'read from {} `{}`'

    @classmethod
    def read_from(cls, _type, name):
        assert _type in {'reg', 'wire'}
        return cls.read_from_str.format(_type, name)

    @class_property
    def format_comment_str(cls):
        return '# data[{}] : {}\n'

    @classmethod
    def format_comment(cls, comment):
        s = []
        for bit, c in comment.items():
            s.append(cls.format_comment_str.format(bit, c))

        return ''.join(s)

    @class_property
    def __check_tile_str(cls):
        return '@ tile ({}, {}) {}'

    @classmethod
    def __check_tile(cls, row, col, s):
        # currently still printing (x, y) i.e. (col, row). So that it matches p_state and r_state
        # we can transition to row/col eventually
        if row is not None and col is not None:
            return cls.__check_tile_str.format(col, row, s)
        else:
            return s
