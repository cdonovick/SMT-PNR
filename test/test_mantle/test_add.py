import delegator
import os
os.environ["MANTLE"] = "coreir"
import magma as m
from magma.testing import check_files_equal
from mantle.coreir.arith import DefineAdd, DefineSub, DefineNegate, DefineASR
from magma.testing.newfunction import testvectors as function_test
from magma.simulator.python_simulator import testvectors as simulator_test


def test_add():
    width = 16
    m.compile("build/test_add16", DefineAdd(width), output="coreir")
    assert check_files_equal(__file__,
            "build/test_add16.json", "gold/test_add16.json")

    dir_path = os.path.dirname(os.path.realpath(__file__))
    delegator.run("cgra-mapper build/test_add16.json build/test_add16_mapped.json", cwd=dir_path)
    assert check_files_equal(__file__,
            "build/test_add16_mapped.json", "gold/test_add16_mapped.json")


    result = delegator.run("""
        ../../run_pnr.py                                         \
            gold/test_add16_mapped.json                          \
            cgra_info.txt                                        \
            --bitstream build/test_add16_mapped_pnr_bitstream    \
            --annotate build/test_add16_mapped_annotated         \
            --debug                                              \
            --print --coreir-libs cgralib
    """, cwd=dir_path)
    if result.return_code:
        print(result.out)
        print(result.err)
    assert not result.return_code
