from hypothesis.strategies import lists, integers, tuples, dictionaries
from hypothesis import given
from qcware_transpile.helpers import (
    map_seq_to_seq,
    prepend_index_to_domain,
    reverse_map,
)

equal_length_lists = integers(min_value=0, max_value=10).flatmap(
    lambda n: tuples(
        lists(integers(), min_size=n, max_size=n),
        lists(integers(), min_size=n, max_size=n),
    )
)


@given(equal_length_lists)
def test_map_seq_to_seq(sequences):
    s1, s2 = sequences
    result = map_seq_to_seq(s1, s2)
    for i in range(len(s1)):
        assert s1[i] in result
        assert s2[i] in result[s1[i]]


@given(index=integers(), f=dictionaries(keys=integers(), values=integers()))
def test_prepend_index_to_domain(index, f):
    result = prepend_index_to_domain(index, f)
    for k, v in result.items():
        assert v == f[k[1]]


@given(dictionaries(integers(), integers()))
def test_reverse_map(f):
    rm = reverse_map(f)
    for k, v in rm.items():
        for item in v:
            assert k == f[item]
