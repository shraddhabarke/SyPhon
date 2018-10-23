# -*- coding: utf-8 -*-

import json

features = ["palatal", "palletized", "sibilant", "sonorant", "coronal", "retroflex", "creaky", "risingTone", "highTone", "lowTone", "middleTone", "long", "vowel", "tense", "lax", "high", "middle", "low", "front", "central", "back", "rounded", "bilabial", "stop", "voice", "fricative", "labiodental", "dental", "alveolar", "labiovelar", "velar", "nasal", "uvular", "glide", "liquid", "lateral", "trill", "flap", "affricate", "alveopalatal", "anterior", "aspirated", "unreleased", "laryngeal", "pharyngeal", "syllableBoundary", "wordBoundary", "continuant", "syllabic", "delayedRelease"]

#Ellis's features.
symbol = "symbol"
palatal = "palatal"
palletized = "palletized"
sibilant = "sibilant"
sonorant = "sonorant"
coronal = "coronal"
retroflex = "retroflex"
creaky = "creaky"
risingTone = "risingTone"
highTone = "highTone"
lowTone = "lowTone"
middleTone = "middleTone"
longVowel = "long"
vowel = "vowel"
tense = "tense"
lax = "lax"
high = "high"
middle = "middle"
low = "low"
front = "front"
central = "central"
back = "back"
rounded = "rounded"
bilabial = "bilabial"
stop = "stop"
voice = "voice"
fricative = "fricative"
labiodental = "labiodental"
dental = "dental"
alveolar = "alveolar"
#labiovelar = "labiovelar"
velar = "velar"
nasal = "nasal"
uvular = "uvular"
glide = "glide"
liquid = "liquid"
lateral = "lateral"
trill = "trill"
flap = "flap"
affricate = "affricate"
alveopalatal = "alveopalatal"
anterior = "anterior"
aspirated = "aspirated"
unreleased = "unreleased"
laryngeal = "laryngeal"
pharyngeal = "pharyngeal"
syllableBoundary = "syllableBoundary"
wordBoundary = "wordBoundary"
continuant = "continuant"
syllabic = "syllabic"
delayedRelease = "delayedRelease"

#Ellis's sophisticated feature inventory.
symbols = {
    # unrounded vowels
    u"i": [voice,tense,high],
    u"ɨ": [voice,tense,high,back],
    u"ɩ": [voice,high],
    u"e": [voice,tense],
    u"ə": [voice,back],
    u"ɛ": [voice],
    u"æ": [voice,low,tense],
    u"a": [voice,low,tense,back],
    u"ʌ": [voice,back,tense],
    # rounded vowels
    u"u": [voice,tense,high,back,rounded],
    u"ü": [voice,tense,high,rounded],
    u"ʊ": [voice,high, back, rounded],
    u"o": [voice,tense,back,rounded],
    u"ö": [voice,tense,rounded],
    u"ɔ": [voice,back,rounded],
    #possibly missing are umlauts

    # consonance
    u"p": [anterior,],
    u"p|": [anterior,unreleased],
    u"p^h": [anterior,aspirated],
    u"b": [anterior,voice],
    u"f": [anterior,continuant],
    u"v": [anterior,continuant,voice],
    u"β": [anterior,continuant,voice],
    u"m": [anterior,nasal,voice,sonorant],#continuant],
    u"m̥": [anterior,nasal,sonorant],#,continuant],
    u"θ": [anterior,continuant,coronal],
    u"d": [anterior,voice,coronal],
   #u"d̪": [voice,coronal],
    u"d^z": [anterior,coronal,voice,delayedRelease],
    u"t": [anterior,coronal],
    #u"t̪": [coronal],
    u"t|": [anterior,coronal,unreleased],
    u"t^s": [anterior,coronal,delayedRelease],
    u"t^h": [anterior,aspirated,coronal],
    u"ṭ": [anterior,retroflex,coronal],
    u"ḍ": [anterior,retroflex,coronal,voice],
    u"ṛ": [anterior,retroflex,coronal,voice,continuant],
    u"ð": [anterior,continuant,voice,coronal],
    u"z": [anterior,continuant,voice,coronal, sibilant],
    u"ǰ": [voice,coronal,sibilant],#alveopalatal,
    u"ž": [continuant,voice,coronal, sibilant],#alveopalatal,
    u"s": [anterior,continuant,coronal, sibilant],
    u"n": [anterior,nasal,voice,coronal,sonorant],#continuant],
    u"ṇ": [anterior,retroflex,nasal,voice,sonorant],#continuant],
    u"n̥": [anterior,nasal,coronal,sonorant],#continuant],
    u"ñ": [nasal,voice,coronal,sonorant],#continuant],alveopalatal,
    u"š": [continuant,coronal, sibilant],#alveopalatal,
    u"c": [palatal,coronal], # NOT the same thing as palletized
    u"č": [coronal,sibilant],#alveopalatal,
    u"č^h": [coronal,sibilant,aspirated],#alveopalatal,
    u"k": [back,high],
    u"k|": [back,high,unreleased],
    u"k^h": [back,high,aspirated],
    u"k^y": [back,high,palletized],
    u"x": [back,high,continuant],
    u"X": [back,continuant], # χ
    u"x^y": [back,high,continuant,palletized],
    u"g": [back,high,voice],
    u"g^y": [back,high,voice,palletized],
    u"ɣ": [back,high,continuant,voice],
    u"ŋ": [back,high,nasal,voice,sonorant],#continuant],
    u"q": [back],
    u"N": [back,nasal,voice],#continuant],
    u"G": [back,voice],
    u"ʔ": [sonorant,low],#laryngeal,
    u"h": [continuant,sonorant,low],#laryngeal,
    u"ħ": [back, low,continuant,sonorant],

    # glides
    u"w": [glide,voice,sonorant,continuant],
    u"y": [glide,palletized,voice,sonorant,continuant],
    u"j": [glide,palletized,voice,sonorant,continuant],

    # liquids
    u"r": [liquid,voice,coronal,sonorant,continuant],
    u"r̃": [liquid,trill,voice,coronal,sonorant,continuant],
    u"r̥̃": [liquid,trill,coronal,sonorant,continuant],
    u"ř": [liquid,flap,voice,coronal,sonorant,continuant],
    u"l": [liquid,lateral,voice,coronal,sonorant,continuant],
#    u"̌l": [liquid,lateral,voice,coronal,sonorant],

    # I'm not sure what this is
    # I think it is a mistranscription, as it is in IPA but not APA
    # u"ɲ": []

    u"ʕ": [back, low, voice,continuant],
    u"-": [syllableBoundary],
    u"##": [wordBoundary],
}
