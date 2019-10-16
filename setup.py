#!/usr/bin/env python3
import sys
import shutil
from enum import Enum
from setuptools import setup, find_packages

class Errors(Enum):
  z3_NOT_FOUND = 1
  z3_BINDINGS_NOT_FOUND = 2

def check_z3():
  if shutil.which('z3') is None:
    print(
      'z3 executable not found.\n'
      'Have you installed z3?\n'
      'Make sure you install with the `--python` flag.\n'
      'See https://github.com/Z3Prover/z3#python'
    )
    sys.exit(Errors.z3_NOT_FOUND.value)

  try:
    import z3
  except ImportError:
    print(
      'z3 bindings not found.\n'
      'Have you installed z3 with the `--python` flag?\n'
      'See https://github.com/Z3Prover/z3#python'
    )
    sys.exit(Errors.z3_BINDINGS_NOT_FOUND.value)

check_z3()

setup(
  name='phonosynthesis',
  version='0.1.0',
  packages=find_packages(),
  python_requires='~=3.6',
  install_requires=[
    'flask~=1.0',
    'python-dotenv~=0.10',
  ],

  # TODO: Update this with actual entry points for cmdline tools
  entry_points={},

  project_urls={
    'Demo': 'https://goto.ucsd.edu/phonosynth',
    'Source': 'https://github.com/shraddhabarke/Phonosynthesis',
  },
)
