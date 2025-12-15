import cProfile
import re

TEST_OBJECTS = ["../examples/bv.py"]

for object_path in TEST_OBJECTS:
    cProfile.run(f"{object_path}")
