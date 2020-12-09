from hypothesis.strategies import lists, integers, tuples
from hypothesis import given
from qcware_transpile.helpers import map_seq_to_seq

equal_length_lists = integers(min_value=0, max_value=10).flatmap(
    lambda n: tuples(lists(integers(), min_size=n, max_size=n),
                     lists(integers(), min_size=n, max_size=n)))


@given(equal_length_lists)
def test_map_seq_to_seq(sequences):
    s1, s2 = sequences
    result = map_seq_to_seq(s1, s2)
    for i in range(len(s1)):
        assert s1[i] in result
        assert s2[i] in result[s1[i]]
