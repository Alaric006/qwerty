# Documentation


# Profiled program using cProfile
```python3 -m cProfile -o results.prof ../examples/bv.py 10```

Installed SnakeViz:
```pip install snakeviz```
snakeviz filename.prof

```pip install py-spy```

```npm install -g speedscope``` OR view at "https://www.speedscope.app/"

```samply record -- python ../examples/bv.py 1000```

```samply record --iteration-count 500 --jit-markers -- python ../examples/bv.py 1000```

```austin -o austin-results.prof python3 ../examples/bv.py 1000```

```py-spy record -o py-spy-results.prof --native --format speedscope -- python sampler.py```

## Notes
~81% of call time to bv.py is on line 91 of /qwerty_pyrt/python/qwerty/kernel.py -> __call___ func. Says: method call of builtsints.Program objects, black hole because its Rust / C++ code?


 - kernel.py is a treasure trove of cool and terrifying code. Python can understand its own AST, look at _jit. 

 - Problem with cPython is that it only shows native python code (not Rust or C++, where we spend the majority of our compiler time)

 - [py-spy](https://github.com/benfred/py-spy) seems like a good option

