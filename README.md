PhonoSynthesis infers phonological rules given a set of input output
transformations. Phonological rules are general principles that apply to
all words of a natural class that is defined in terms of phonological
properties. The features of phonetic sounds are encoded as constraint
variables in a SAT formula. PhonoSynthesis solves for a satisfying
assignment which is equivalent to inferring the phonological rule.

## Installation

We recommend installing all dependencies (including z3) in a [Python
virtual environment](https://virtualenv.readthedocs.io/en/latest/).

This project requires Python 3.6 or later.

### Install z3

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
$ pip install -e .
```

## Usage

Start the development server (in the project root).

``` shellsession
$ flask run
```

The web interface is then available at <http://localhost:5000>.

## Conditional Inference

The input to condition inference is the set of pairs (triple, changed), where triple is a phone trigram and the label can be True or False indicating whether the triple changed or not. For example, in the Turkish dataset: ```deniz``` changes to ```denizlar``` and ```dib``` changes to ```diplar```
from the change inference, we learn which triples change and which do not. <br>
An example of a triple that does not change - ```niz``` to ```niz```  <br>
An example of a triple that does change - ```ib#``` to ```ip```  <br>

Left Context - ```{'voice': '+', 'front': '0', 'nasal': '+', 'back': '0', 'round': '0', 'consonant': '+', 'continuant': '-', 'coronal': '+', 'advanced tongue root': '0', 'distributed': '-', 'delayed release': '0', 'constricted glottis': '-', 'approximant': '-', 'labial': '-', 'high': '0', 'strident': '0', 'anterior': '+', 'dorsal': '-', 'spread glottis': '-', 'sonorant': '+', 'lateral': '-', 'syllabic': '-', 'low': '0', 'long': '-', 'primary stress': '-', 'secondary stress': '-', 'stress': '-', 'word boundary': '0', 'deleted': '-'}```

Target - ```{'voice': '+', 'front': '+', 'nasal': '-', 'back': '-', 'round': '-', 'consonant': '-', 'continuant': '+', 'coronal': '-', 'advanced tongue root': '+', 'distributed': '0', 'delayed release': '0', 'constricted glottis': '-', 'approximant': '+', 'labial': '-', 'high': '+', 'strident': '0', 'anterior': '0', 'dorsal': '+', 'spread glottis': '-', 'sonorant': '+', 'lateral': '-', 'syllabic': '+', 'low': '-', 'long': '-', 'primary stress': '-', 'secondary stress': '-', 'stress': '-', 'word boundary': '0', 'deleted': '-'}```

Right Context - ```{'voice': '+', 'front': '0', 'nasal': '-', 'back': '0', 'round': '0', 'consonant': '+', 'continuant': '+', 'coronal': '+', 'advanced tongue root': '0', 'distributed': '-', 'delayed release': '+', 'constricted glottis': '-', 'approximant': '-', 'labial': '-', 'high': '0', 'strident': '+', 'anterior': '+', 'dorsal': '-', 'spread glottis': '-', 'sonorant': '-', 'lateral': '-', 'syllabic': '-', 'low': '0', 'long': '-', 'primary stress': '-', 'secondary stress': '-', 'stress': '-', 'word boundary': '0', 'deleted': '-'}``` <br>

To encode the constraints to z3, for each feature we use six control variables, which represent the three positions that a feature can appear in a rule and the two values it can take. More concretely for the above case, the constraints are -

``` And(Not(advanced tongue root left +), Not(advanced tongue root left -), Not(advanced tongue root center -), Not(advanced tongue root right +), Not(advanced tongue root right -), Not(constricted glottis left +), Not(constricted glottis center +), Not(constricted glottis right +), Not(primary stress left +), Not(primary stress center +), Not(primary stress right +), Not(high left +), Not(high left -), Not(high center -), Not(high right +), Not(high right -), Not(stress left +), Not(stress center +), Not(stress right +), Not(coronal left -), Not(coronal center +),Not(coronal right -), Not(front left +), Not(front left -), Not(front center -), Not(front right +), Not(front right -), Not(dorsal left +), Not(dorsal center -), Not(dorsal right +), Not(continuant left +), Not(continuant center -), Not(continuant right -), Not(labial left +), Not(labial center +), Not(labial right +), Not(anterior left -), Not(anterior center +), Not(anterior center -), Not(anterior right -), Not(delayed release left +), Not(delayed release left -), Not(delayed release center +), Not(delayed release center -), Not(delayed release right -), Not(word boundary left +), Not(word boundary left -), Not(word boundary center +),Not(word boundary center -),Not(word boundary right +), Not(word boundary right -), Not(deleted left +), Not(deleted center +), Not(deleted right +), Not(secondary stress left +), Not(secondary stress center +), Not(secondary stress right +), Not(strident left +), Not(strident left -), Not(strident center +), Not(strident center -), Not(strident right -), Not(lateral left +), Not(lateral center +), Not(lateral right +), Not(syllabic left +), Not(syllabic center -), Not(syllabic right +), Not(long left +), Not(long center +), Not(long right +), Not(sonorant left -), Not(sonorant center -), Not(sonorant right +), Not(spread glottis left +), Not(spread glottis center +), Not(spread glottis right +), Not(distributed left +), Not(distributed center +), Not(distributed center -), Not(distributed right +), Not(consonant left -), Not(consonant center +), Not(consonant right -), Not(voice left -), Not(voice center -), Not(voice right -), Not(nasal left -), Not(nasal center +), Not(nasal right +), Not(round left +), Not(round left -), Not(round center +), Not(round right +), Not(round right -), Not(approximant left +), Not(approximant center -), Not(approximant right +), Not(back left +), Not(back left -), Not(back center +), Not(back right +), Not(back right -), Not(low left +), Not(low left -), Not(low center +), Not(low right +), Not(low right -)``` <br>
    
For alpha notation, if the left and the right values for any feature are the same (and not 0) they can be combined into an alpha variable. The alpha constraints for the above triple would be 
  
``` Not(alpha left right advanced tongue root), Not(alpha left right high), Not(alpha left right front), Not(alpha left right continuant), Not(alpha left right delayed release), Not(alpha left right word boundary), Not(alpha left right strident), Not(alpha left right sonorant), Not(alpha left right nasal), Not(alpha left right round), Not(alpha left right back), Not(alpha left right low))```
  
The constraints for simplicity and likelihood are encoded as - <br>

```opt.add(simplicity == simplicity_score * SIMPLICITY_WEIGHT)``` <br>
```opt.add(likelihood == log_num_models * LIKELIHOOD_WEIGHT * n_pos)``` <br>
  
where ```n_pos``` is the number of triples that changed.

## Simplicity Constraints

```FEATURE_PENALTY = 1000; FEATURE_SIMPLICITY_WEIGHT = 5```

Simplicity cost for alpha variable - ```weight = 2 * (FEATURE_PENALTY + FEATURE_SIMPLICITY_WEIGHT * FEATURE_SIMPLICITY[feature])``` <br>

example constraint - ```simplicity cost alpha left right continuant == If(alpha left right continuant, 3090, 0)``` <br>
where 3090 is the weight for the feature ```continuant```

Simplicity cost for features - ```weight = POSITION_WEIGHTS[position] * FEATURE_PENALTY + FEATURE_SIMPLICITY_WEIGHT * ipa_data.FEATURE_SIMPLICITY[feature]```

where ```POSITION_WEIGHTS = {'left': 2, 'center': 1, 'right': 2}```

```Implies(continuant left +, left nonempty)```
```simplicity cost continuant left + == If(continuant left +, 2545, 0)```

```If(left nonempty, 50000, 0)```
```If(right nonempty, 50000, 0)```

#### Feature simplicity calculation per feature


## Likelihood Constraints

