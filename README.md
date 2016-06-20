Main Program
========

#### Compile

```
make
```

This requires a recent ocaml, ocamlfind, ounit and ocamlbuild, preferably installed via opam.

#### Execute
To execute the solver you just need to execute 
```
./solver.native file.smt
```

#### Example
```
# ./solver.native file.smt
sat
y = 2
x = 3
```

#### Options
Available options are :
* `--path-solver` Set the path to the solver
* `-ps`           Alias for -path-solver
* `--op-solver`   Set options for the solver (can be called multiple times)
* `-op`           Alias for -op-solver
* `--verbose`     be verbose
* `-v`            be verbose 


Tests
========

### Unit Tests
```
make tests
```

### External Tests

#### Compile

```
make exttests
```

#### Execute

To execute it, you have two possibilities, each one will read lines having the following pattern : `"path_to_file\filename.smt" "expected result"` corresponding to the file on which the solver will be executed and to the expected result. The two possibilities are :
* give each test one by one on the standard input

#### Example
```
# ./exttests.native
"examples/test1.smt" "sat y = 2 x = 3"

Testing : ./solver.native examples/test1.smt  

Expected : sat y = 2 x = 3
Obtained : sat y = 2 x = 3

Test OK

-----------

"examples/test1.smt" "sat y = 2 x = 4"
Testing : ./solver.native examples/test1.smt  

Expected : sat y = 2 x = 4
Obtained : sat y = 2 x = 3

Test Not OK

-----------
```
* Or fill a file *filename*.test where each line correspond to a file to read and to the expected result

```
# cat simpletests.test 
"examples/test1.smt" "sat y = 2 x = 3"
"examples/test2.smt" "unsat"

# ./exttests.native simpletests.test 
Testing : ./solver.native examples/test1.smt  

Expected : sat y = 2 x = 3
Obtained : sat y = 2 x = 3

Test OK

-----------

Testing : ./solver.native examples/test2.smt  

Expected : unsat
Obtained : unsat

Test OK

-----------

#
```

#### Options
* `--path-solver` This option is sent to `./solver.native` for each test
* `-ps`           This option is sent to `./solver.native` for each test
* `--op-solver`   This option is sent to `./solver.native` for each test
* `-op`           This option is sent to `./solver.native` for each test

Some of the tests are broken atm.
