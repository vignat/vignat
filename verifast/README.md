# Files

* map.c - A hash-map (int->int) C certified implementation.
* nat\_seq.gh - An auxilary theory of natural sequences, represented as lists of decreading integer numbers e.g. `(5 (4 (3 (2 (1 (0 nil))))))`;
* nth_prop.gh - An auxilary set of lemmas reasoning about predicates applied to sets of indexed array sells.
* stdex.gh - An extension of VeriFast `list.gh` and `listex.gh`, adding more lemmas about `update`, `nth`, `cons` etc.

# Use

You will need [VeriFast](http://people.cs.kuleuven.be/~bart.jacobs/verifast/) program verifier (tested on VeriFast 15.05). It comes in binaries. You can obtain it by
  ```bash
      $ wget http://people.cs.kuleuven.be/~bart.jacobs/verifast/verifast-15.05.tar.gz
      $ tar -xf verifast-15.05.tar.gz
      $ export PATH=$PWD/verifast-15.05/bin:$PATH
  ```

Then just type:
  ```bash
      $ verifast -shared map.c
  ```

It will check that C code in map.c is a correct implementation of the specifications, given by the `//@ requires`/`//@ ensures` comments.