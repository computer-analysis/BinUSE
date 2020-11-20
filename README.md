# BinUSE
This is the prototype implementation of BinUSE.

# Requirement
`python3 (>= 3.6.5)` and `ida pro (7.3)`

`pip install angr==8.20.7.6`

`pip install zss`

# Usage of BinUSE
Using ida to do static analysis. Please change the path to `idat64` in scripts `./collect_functions.sh` and `./collect_functions_refs.sh`

insert following code to `angr/state_plugins/symbolic_memory.py`, around line 390.

```
    if a is not None:
        # added by BinUSE
        if hasattr(self.state, 'memaddr'):
            self.state.memaddr.get_relative_symbol(e)
        # end BinUSE
        return a
```

Then run

`sh ./collect_functions.sh [path/to/bin1]`. If this script works, you will find a directory named with `[path/to/bin1]_functions`.

`sh ./collect_functions_refs.sh [path/to/bin1]`. If this script works, you will find a directory named with `[path/to/bin1]_functions_refs`

Repeat this process for `bin2`.

Then run

`python main.py [path/to/bin1] [path/to/bin2] > test.info`

After finishing the comparison, result will be printed to the `stdout`

# Analyze the result
assume you have the output file `test.info`

run `python ./analysis/process_info.py test.info [dict|list]`, then a file `test.info.pkl` is saved on disk.

To understand the dumped `*.plk` file, please read the code in `./analysis/process_info.py`.

To optimize DNN-based result, please run `python ./analysis/optimize.py [use.pkl] [dnn.pkl] [path/to/dump/the/optimized/dictionary]`

