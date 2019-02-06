PhonoSynthesis infers phonological rules given a set of input output transformations. Phonological rules are general principles that apply to all words of a natural class that is defined in terms of phonological properties. The features of phonetic sounds are encoded as constraint variables in a SAT formula. PhonoSynthesis solves for a satisfying assignment which is equivalent to inferring the phonological rule.

## Installation

We recommend installing all dependencies (including Z3) in a [Python virtual
environment](https://virtualenv.readthedocs.io/en/latest/).

### Install Z3

``` shellsession
$ git clone https://github.com/Z3Prover/z3.git
$ cd z3
$ python scripts/mk_make.py --python
$ cd build
$ make
$ make install
```

### Clone the repo and install Python dependencies

```shellsession
$ git clone https://github.com/shraddhabarke/Phonosynthesis.git
$ cd Phonosynthesis
$ pip install -r requirements.txt
```

## Usage

Start the development server (in the project root).

``` shellsession
$ flask run
```

The web interface is then available at http://localhost:5000.
