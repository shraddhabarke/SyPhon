PhonoSynthesis infers phonological rules given a set of input output transformations. Phonological rules are general principles that apply to all words of a natural class that is defined in terms of phonological properties. The features of phonetic sounds are encoded as constraint variables in a SAT formula. PhonoSynthesis solves for a satisfying assignment which is equivalent to inferring the phonological rule.

## Installation instructions

Install the dependencies.

```
$ cd demo && pip install -r requirements.txt
```

Install z3 locally from [here](https://github.com/Z3Prover/z3)

Now run the Flask application! 

```
    $ export FLASK_APP=app.py
    $ export FLASK_ENV=development
    $ flask run
    * Debug mode: off
    * Running on http://127.0.0.1:5000/ (Press CTRL+C to quit)
```
