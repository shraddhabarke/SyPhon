# -*- coding: utf-8 -*-
from features import *

def transposeInflections(inflections):
    return [ tuple([ inflections[x][y] for x in range(len(inflections)) ]) for y in range(len(inflections[0])) ]

def stripConsonants(matrix):
    def s(x):
        if x == None: return x
        canonical = []
        for p in tokenize(x):
            if p == u'##': canonical.append(p)
            #elif 'vowel' in featureMap[p]: canonical.append(p)
            elif 'vowel' in featureMap[p] and not 'highTone' in featureMap[p]: canonical.append(u'a')
            elif 'vowel' in featureMap[p] and 'highTone' in featureMap[p]: canonical.append(u'á')
        return u''.join(canonical)
    return [tuple(map(s,i)) for i in matrix ]

def processMorphology(stems, inflections, dictionary):
    # map from (stem, inflection) to surface form
    surfaces = {}
    for surface, translation in dictionary.iteritems():
        found = False
        for stem in stems:
            for inflection in inflections:
                if inflection + ' ' + stem == translation or stem + ' ' + inflection == translation or stem + inflection == translation:
                    if found:
                        print "DEGENERACY:"
                        print "Trying to parse the mapping:",surface, translation
                        print "found that it is compatible with",stem, inflection
                        print "previously found it to be",found
                    assert not found
                    found = (stem, inflection)
                    surfaces[(stem, inflection)] = surface.replace(' ','##').replace(u'ɗ',u'd').replace(u'ɓ',u'b')
        if not found:
            print "Could not explain",surface, translation
            assert False
    # Construct the inflection matrix
    matrix = [ tuple([ surfaces.get((stem, inflection),None) for inflection in inflections ])
             for stem in stems ]
    return matrix
            
            
                



class Problem():
    def __init__(self,description,data,parameters = None,solutions = []):
        self.parameters = parameters
        self.description = description
        self.solutions = solutions
        if parameters:
            self.data = [ x.replace(u"’",u"") for x in data ]
        else:
            self.data = [ tuple([ (None if x == None else x.replace(u"’",u""))
                                  for x in inflections ])
                          for inflections in data ]

        for l in description.split("\n"):
            l = l.strip().replace(':','')
            if len(l) > 0:
                if l[0] in '0123456789': l = ' '.join(l.split(' ')[1:])
                self.languageName = l
                break
            

        # As a sanity check we try to tokenize all of the data
        # This is to make sure that as we define each problem we check to see if it only uses things for which we know the features
        for d in self.data:
            if isinstance(d,basestring):
                tokenize(d)
            else:
                for x in d:
                    if x != "~" and x != None:
                        tokenize(x)
        # If this is an alternation problem
        if parameters and "alternations" in parameters:
            if False:
                ps = set([ p for w in data for p in tokenize(w) ])
                print "Number of distinct phonemes: %d" % len(ps)
                fs = set([ f  for p in ps for f in featureMap[p] ])
                print "Number of distinct features: %d" % len(fs)
                print " ==  ==  == "
        elif not parameters:#this is a matrix problem
            for inflections in self.data:
                assert len(inflections) == len(self.data[0])

    def __str__(self):
        from utilities import formatTable
        l = []
        patterns = {tuple(s is None for s in ss )
                    for ss in self.data }
        for p in patterns:
            for ss in self.data:
                if tuple(s is None for s in ss ) == p:
                    l.append(map(unicode,ss))
        return formatTable(l)
        return u"\n".join(l)
                    

# Learning tone patterns
toneProblems = []
toneProblems.append(Problem(u'''
Explain HLM tone pattern.
''',
                            [u"áu`i¯",
                             u"íe`i¯",
                             u"óa`u¯",
                             u"íu`e¯",
                             u"úi`a¯"],
                            {"type": "alternation",
                             "alternations": [dict([ (toned, toned[:-1])
                                                     for toned in featureMap.keys()
                                                     if highTone in featureMap[toned] or
                                                     lowTone in featureMap[toned] or
                                                     middleTone in featureMap[toned] ])]}))

# Chapter 3: alternation problems
alternationProblems = []

alternationProblems.append(Problem(
    u'''
Kikurai
Provide rules to explain the distribution of the consonants [β,r,ɣ] and [b,d,g] in the following data. Accents mark tone: acute is H tone and ‘hacek’ [   ̌] is rising tone.
    [+voice, +fricative] > [+stop, -fricative] / [+nasal] _
    
    [ -laryngeal -glide -nasal -vowel -alveopalatal ] ---> [ -fricative -approximate +stop -sonorant -central -liquid ] / [ +nasal ] _ 
    ''',
    [u"aβaánto",#"people"),
     u"aβamúra",#"young men"),
     u"amahííndi",#"corn cobs"),
     u"amakɛ́ɛ́ndɔ",#"date fruits"),
     u"eβǎ",#"forget"),
     u"eeŋgwé",#"leopard"),
     u"eɣǎ",#"learn"),
     u"ekeβwɛ́",#"fox"),
     u"hoorá",#"thresh"),
     u"iβiɣúrúβe",#"small pigs"),
     u"iβirúúŋgúuri",#"soft porridges"),
     u"uɣusíri",#"huge rope"),
     u"βáinu",#"you (pl)"),
     u"βoryó",#"on the right"),
     u"ičiiŋgɛ́na",#"grinding stones"),
     u"ičiiŋgúrúβe",#"pig"),
     u"ɣaβǎ",#"share!"),
     u"ičiiŋgúta",#"walls"),
     u"βɛrɛká",#"carry a child!"),
     u"iɣitúúmbe",#"stool"),
     u"ɣúúká",#"ancestor"),
     u"remǎ",#"weed!"),
     u"rɛɛntá",#"bring!"),
     u"oβoɣááká",#"male adulthood"),
     u"oβotééndééru",#"smoothness"),
     u"okoɣéémbá",#"to cause rain"),
     u"okoómbára",#"to count me"),
     u"okoβára",#"to count"),
     u"okoóndɔ́ɣa",#"to bewitch me"),
     u"okorɔ́ɣa",#"to bewitch"),
     u"romǎ",#"bite!"),
     u"teɣetá",#"be late!"),
     u"ukuúmbuuryá",#"to ask me"),
     u"uruɣúta"], #"wall"
    {"type": "alternation",
     "alternations": [{u"b": u"β",
                       u"d": u"r",
                       u"g": u"ɣ"}]}))



alternationProblems.append(Problem(
u'''
2: Modern Greek
Determine whether the two segments [k] and [k^y] are contrastive or are governed by rule; similarly, determine whether the difference between [x] and [x^y] is contrastive or predictable. If the distribution is rule-governed, what is the rule and what do you assume to be the underlying consonants in these cases?
Solution:
{x^y,k^y} occur only when there is a front vowel to the right
[ -liquid +velar ] ---> [ +palatal -alveolar -nasal -liquid -voice ] /  _ [ +front ]
''',
    [u"kano",#"do"),
     u"kori",#"daughter"),
     u"xano",		#"lose"),
     u"xori",		#"dances"),
     u"x^yino",		#"pour"),
     u"k^yino",		#"move"),
     u"krima",		#"shame"),
     u"xrima",		#"money"),
     u"xufta",		#"handful"),
     u"kufeta",		#"bonbons"),
     u"kali",		#"charms"),
     u"xali",		#"plight"),
     u"x^yeli",		#"eel"),
     u"k^yeri",		#"candle"),
     u"x^yeri",		#"hand"),
     u"ox^yi"],
    {"type": "alternation",
     "alternations": [{u"k^y": u"k",
                       u"x^y": u"x"}]}))		#"no")

alternationProblems.append(Problem(
u'''
3: Farsi
Describe the distribution of the trill [r̃] and the flap [ř].
Solution found by system:
trill > flap / [ +vowel ] _ [ -alveolar ]
 / [ +unrounded ] _ [ +vowel ]
[ +liquid +voice ] ---> [ -trill -low +flap ] / [ +sonorant ] _ [ -alveolar ]
''',
    [
	u"ær̃teš",#		"army"),
        u"far̃si",#		"Persian"),
	u"qædr̃i",#		"a little bit"),
        u"r̃ah",#		"road"),
	u"r̃ast",#		"right"),
        u"r̃iš",#		"beard"),
	u"ahar̥̃",#		"starch"),
        u"axær̥̃",#		"last"),
	u"hær̃towr̥̃",#	"however"),
        u"šir̥̃",#		"lion"),
	u"ahaři",#		"starched"),
        u"bæřadær̥̃",#	"brother"),
	u"čeřa",#		"why?"),
        u"dařid",#		"you have"),
	u"biřæng",#		"pale"),
        u"šiřini"],#		"pastry")
    {"type": "alternation",
     "alternations": [{u"ř": u"r̃"}]}))

alternationProblems.append(Problem(
    u'''
4: Osage
What rule governs the distribution of [d] versus [ð] in the following data?
    d occurs when there is [a,á] to the right
    ð occurs when there is [i,e] to the right
    ð > d / _ [+low] (my solution)
    d > ð / _ [ +central ] (systems solution)
    [ -alveolar +coronal -tense -front -alveopalatal +voice ] ---> [ -fricative +alveolar +stop -dental ] /  _ [ +low ]
''',
    [u"dábrĩ",#		"three"),
     u"áðik^hã žã",#	"he lay down"),
     u"dačpé",#		"to eat"),
     u"čʔéðe",#		"he killed it"),
     u"dakʔé",#		"to dig"),
     u"ðéze",#		"tongue"),
     u"dálĩ",#		"good"),
     u"ðíe",#		"you"),
     u"daštú",#		"to bite"),
     u"ðíški"],#		"to wash")])
    {"alternations": [{u"ð": u"d"}]}))

alternationProblems.append(Problem(
    u'''
5: Amharic
Is there a phonemic contrast between the vowels [ə] and [ɛ] in Amharic? If not, say what rule governs the distribution of these vowels, and what the underlying value of the vowel is.
"ə" occurs in the contexts:
    {f,r,t,n,g,z,m,d,k,l,b} _ {r,s,n,b,w,d,m,t,g,b,k,č,#}
ɛ occurs in the contexts    :
    {y,š,ž,č,ñ} _ {l,t,g,m,#}
System discovers:
[ -coronal +lax ] ---> [ +tense -front +central -alveopalatal -lax ] / [ -glide -alveopalatal ] _ 
    ''',
    [
	u"fərəs",#		"horse"),
        u"tənəsa",#		"stand up!"),
#	u"yɛlɨš̌lɨš̌",#		"grandchild"),
        u"yɛlɨšlɨš",#		"grandchild"),
        u"mayɛt",#		"see"),
	u"gənzəb",#		"money"),
        u"šɛgna",#		"brave"),
	u"nəñ",#		"I am"),
        u"məwdəd",#	"to like"),
	u"mənnəsat",#	"get up"),
        u"məmkər",#	"advise"),
	u"žɛle",#		"unarmed"),
        u"yɛlləm",#		"no"),
	u"məč",#		"when"),
        u"məst’ət",#		"give"),
	u"fəlləgə",#		"he wanted"),
        u"agəññɛ",#		"he found"),
	u"təməččɛ",#	"it got comfortable"),
        u"mokkərə",#	"he tried"),
	u"k’ažžɛ",#		"he talked in his sleep"),
        u"žɛmmərə",#	"he started"),
	u"lačč’ɛ",#		"he shaved"),
        u"aššɛ",#		"he rubbed"),
	u"bəkk’ələ",#	"it germinated"),
        u"šɛməggələ"],#	"he became old")])
    {"alternations": [{u"ɛ": u"ə"}]}))


alternationProblems.append(Problem(
    u'''
6: Gen
Determine the rule which accounts for the distribution of [r] and [l] in the following data.
    System learns:
    l > r / [ +coronal ] _ [  ]
    My analysis:
l occurs in the context:
    {b,g,ɔ,p,u,a,v,x,h,ŋ,k,#,m,e,w} _
r occurs in the context:
    {s,t,d,č,ñ,z,s,ǰ} _
These are all coronal
[ -middle -nasal +sonorant +coronal ] ---> [ -lateral +approximate ] / [ +coronal ] _     
''',
    [u"agble",#"farm"),
     u"agoŋglo",#"lizard"),
     u"aŋɔli",#"ghost"),
     u"akplɔ",#"spear"),
     u"sabulɛ",#"onion"),
     u"sra",#"strain"),
     u"alɔ",#"hand"),
     u"atitrwɛ",#"red billed wood dove"),
     u"avlɔ",#"bait"),
     u"blafogbe",#"pineapple"),
     u"drɛ",#"stretch arms"),
     u"edrɔ",# "dream"),
     u"exlɔ",#"friend"),
     u"exle",#"flea"),
     u"hlɛ",#"read"),
     u"ŋlɔ",#"write"),
     u"črɔ̃",#"exterminate"),
     u"ñrã",#"be ugly"),
     u"klɔ",#"wash"),
     u"tre",#"glue"),
     u"vlu",#"stretch a rope"),
     u"lɔ",#"like"),
     u"mla",#"pound a drum"),
     u"pleplelu",#"laughing dove"),
     u"wla",#"hide"),
     u"zro",#"fly"),
     u"esrɔ",#"spouse"),
     u"etro",#"scale"),
     u"eñrɔ̃",#"spitting cobra"),
     u"ǰro"],#,   "hint")])
    {"alternations": [{u"l": u"r"}]}))

alternationProblems.append(Problem(
u'''
7: Kishambaa
Describe the distribution of voiced versus voiceless nasals (voiceless nasals are written with a circle under the letter, as in m̥), and voiceless aspirated, voiceless unaspirated and voiced stops in Kishambaa.
Solution found by system:
Nasals become voiced when followed by a voiced phoneme

My analysis:
 ==  ==  == 

Voiced stops occur in the contexts:
{a,m,#,o,n,ŋ} _ {i,u,e,o}
Voiceless stops occur in the contexts:
{#,i,a,o,n̥,m̥} _ {a,o,u,i,e}
These pretty much looks the same so I don't think there is a alternation between voice/voiceless stop

Aspirated stops occur in the contexts:
{n̥,m̥,o} _ {u,e}
Unaspirated stops occur in similar right contexts but don't occur next to voiceless nasals. So I think that they exist underlyingly, and that what we're seeing is that voiceless nasals don't exist underlying.

[ -laryngeal +sonorant -high -low -velar ] ---> [ +voice ] /  _ [ -aspirated ]
''',
    [
	u"tagi",# "egg"),
	u"kitabu",# "book"),
	u"paalika",#"fly!"),
	u"ni",# "it is"),
	u"ŋombe",# "cow"),
	u"matagi",#"eggs"),
	u"dodoa",# "pick up"),
	u"goša",# "sleep!"),
	u"babu",#"skin"),
	u"ndimi",# "tongues"),
	u"ŋgoto",# "heart"),
	u"mbeu",#"seed"),
	u"n̥t^humbii",# "monkey"),
	u"ŋok^huŋguni",# "bedbug"),
	u"m̥p^heho"],#"wind")
    {"alternations": [{u"n̥": u"n",
                      u"m̥": u"m"}]}))


# Problem 8 has Unicode issues
alternationProblems.append(Problem(
    u'''
8: Thai
The obstruents of Thai are illustrated below. Determine what the obstruent phonemes of Thai are ([p, t and k] are unreleased stops). Are [p, t, k] distinct phonemes, or can they be treated as positional variants of some other phoneme? If so, which ones, and what evidence supports your decision? Note that no words begin with [g].
    Solution: the Unicode isn't formatted correctly here, and were not actually seen the problem.
    [ptk] occur only word finally and might be underlying aspirated or not aspirated
    ''',
    [u"bil",#   "Bill"),
     u"müü",#   "hand"),
     u"rak|",#   "love"),
     u"baa",#   "crazy"),
     u"loŋ",#   "go down"),
     u"brüü",#   "extremely fast"),
     u"haa",#   "five"),
     u"plaa",#   "fish"),
     u"dii",#   "good"),
     u"čaan",#   "dish"),
     u"t^hee",#   "pour"),
     u"t^hruumɛɛn",#   "Truman"),
     u"k^hɛŋ",#   "hard"),
     u"panyaa",#   "brains"),
     u"ləəy",#   "pass"),
     u"p^hyaa",#    "[title]"),
     u"lüak|",#   "choose"),
     u"klaaŋ",#   "middle"),
     u"č^hat|",#   "clear"),
     u"traa",#   "stamp"),
     u"riip|",#   "hurry"),
     u"ɔɔk|",#   "exit"),
     u"p^hrɛɛ",#   "silk cloth"),
     u"kiə",#   "wooden shoes"),
     u"k^hwaa",#   "right side"),
     u"kɛɛ",#   "old"),
     u"dray",#   "drive (golf)"),
     u"düŋ",#   "pull"),
     u"kan",#   "ward off"),
     u"čuək|",#   "pure white"),
     u"p^hleeŋ",#   "song"),
     u"č^han",#   "me"),
     u"staaŋ",#   "money"),
     u"rap|",#   "take"),
     u"yiisip|",#   "twenty"),
     u"p^haa",#   "cloth"),
     u"k^haa",#   "kill"),
     u"dam",#   "black"),
     u"raay",#   "case"),
     u"tit|",#   "get stuck"),
     u"sip|",#   "ten"),
     u"pen"],#,   "alive")])
    {"alternations": [{u"p|": u"p",
                       u"t|": u"t",
                       u"k|": u"k"}]}))

alternationProblems.append(Problem(
u'''
9: Palauan
Analyse the distribution of ð, θ and d in the following data. Examples of the type ‘X ~ Y’ mean that the word can be pronounced either as X or as Y, in free variation.
{ð,d} > θ / _#
ð > d / #_, optionally
Systems finds symmetric solution of:
[ +dental -unrounded -liquid -tense -voice ] ---> [ -fricative +alveolar +stop -dental +voice ] / # _ [  ]
todo: incorporate optional rules
''',
    [u"kəðə",	#"we (inclusive)"
     u"bəðuk",	#"my stone"
#     ("~", u"ðiak", u"diak"),	#"negative verb"
     u"ðiak", u"diak",
     u"maθ"	#"eye"
     u"tŋoθ",	#"tattoo needle"
#     ("~", u"ðe:l", u"de:l"),	#"nail"
     u"ðe:l", u"de:l",
#     ("~", u"ðiosəʔ", u"diosəʔ"),#	"place to bathe"),
     u"ðiosəʔ", u"diosəʔ",
#     ("~", u"ðik", u"dik"),#	"wedge"),
     u"ðik", u"dik",
     u"kuθ",	#"louse"
     u"ʔoðiŋəl",	#"visit"
     u"koaθ",	#"visit"
     u"eaŋəθ",	#"sky"
     u"ŋərarəðə",	#"a village"
     u"baθ",	#"stone"
     u"ieðl"	#"mango"
     u"ʔəðip",	#"ant"
     u"kəðeb",	#"short"
     u"məðəŋei",	#"knew"
     u"uðouθ",	#"money"
     u"olðak"],	#"put together"
    {"alternations": [{u"θ": u"d"}]}))

alternationProblems.append(Problem(
    u'''
10: Quechua (Cuzco dialect)
	Describe the distribution of the following four sets of segments: k, x, q, χ; ŋ, N; i, e; u, o. Some pairs of these segments are allophones (positional variants) of a single segment. You should state which contrasts are phonemic (unpredictable) and which could be predicted by a rule. For segments which you think are positional variants of a single phoneme, state which phoneme you think is the underlying variant, and explain why you think so; provide a rule which accounts for all occurrences of the predictable variant. (Reminder: N is a uvular nasal).
    [ +sonorant +velar ] ---> [ +uvular -low -sonorant -front -liquid -velar ] /  _ [ +uvular ]
    [ -middle +front -liquid +voice ] ---> [ -high +middle ] / [ -palatal -aspirated -nasal ] _ [ -fricative -bilabial ]* [ -glide -nasal -coronal ]
''',
    [
	u"qori",	#"gold"
        u"čoXlu",	#"corn on the cob"
	u"q’omir",	#"green"
        u"niŋri",	#"ear"
	u"moqo",	#"runt"
        u"hoq’ara",	#"deaf"
	u"p^hulyu",	#"blanket"
        u"yuyaŋ",	#"he recalls"
	u"tulyu",	#"bone"
        u"api",	#"take"
	u"suti",	#"name"
        u"oNqoy",	#"be sick!"
	u"čilwi",	#"baby chick"
        u"č^hičiŋ",	#"be whispers"
	u"č^haNqay",	 #"granulate"
        u"aNqosay", 	#"toast"
	u"qečuŋ",	#"he disputes"
        u"p’isqo",	#"bird"
	u"musoX",	#"new"
        u"čuŋka",	#"ten"
	u"yaNqaŋ", 	#"for free"
        u"čulyu",	#"ice"
	u"qhelya",	#"lazy"
        u"q’eNqo",	#"zigzagged"
	u"čeqaŋ",	#"straight"
        u"qaŋ",	#"you"
	u"noqa",	#"I"
        u"čaxra",	#"field"
	u"čeXniŋ",	#"he hates"
        u"soXta",	#"six"
	u"aXna",	#"thus"
        u"lyixlya",	#"small shawl"
	u"qosa",	#"husband"
        u"qara",	#"skin"
	u"alqo",	#"dog"
        u"seNqa",	#"nose"
	u"karu",	#"far"
        u"atoX",	#"fox"
	u"qaŋkuna",	#"you pl."
        u"pusaX",	#"eight"
	u"t’eXway",	#"pluck"
        u"č’aki",	#"dry"
	u"wateX",	#"again"
        u"aŋka",	#"eagle"
	u"waXtay",	#"hit!"
        u"haku",	#"let’s go"
	u"waqay",	#"tears"
        u"kaŋka",	#"roasted"
	u"waxča",	#"poor"
        u"waleX",	#"poor"
	u"t^hakay",	#"drop"
        u"reXsisqa"],#	"known"
    {"alternations": [{u"ŋ": u"N"},
                      {u"o": u"u"},
                      {u"i": u"e"},
                      ]}))


alternationProblems.append(Problem(
    u'''
11: Lhasa Tibetan
	There is no underlying contrast in this language between velars and uvulars, or between voiced or voiceless stops or fricatives (except /s/, which exists underlyingly). State what the underlying segments are, and give rules which account for the surface distribution of these consonant types. [Notational reminder: [G] represents a voiced uvular stop]
    ''',
    [
	u"aŋgu",	#"pigeon"
	u"aŋṭãã",	#"a number"
	u"aŋba",	#"duck"
	u"apsoo",	#"shaggy dog"
	u"amčɔɔ",	#"ear"
	u"tukṭüü",	#"poison snake"
	u"amto",	#"a province"
	u"ɨɣu",	#"uncle"
	u"ɨmči",	#"doctor"
	u"uṭɨ",	#"hair"
	u"uβɩɩ",	#"forehead"
	u"ea",	#"bells"
	u"embo",	#"deserted"
	u"ʊʊtsi",	#"oh-oh"
	u"qa",	#"saddle"
	u"qaa",	#"alphabet"
	u"qaŋba",	#"foot"
	u"qamba",	#"pliers"
	u"qam",	#"to dry"
	u"qamtoo",	#"overland"
	u"qaaβo",	#"white"
	u"kɨkṭi",	#"belch"
	u"kɨβu",	#"crawl"
	u"kɨɨŋguu",	#"trip"
	u"kik",	#"rubber"
	u"kiṭuu",	#"student"
	u"kɩɩcuu",	#"translator"
	u"kɩɩrii",	#"roll over"
	u"kiiɣuu",	#"window"
	u"ku",	#"nine"
	u"kupcɨ",	#"900"
	u"kupcaa",	#"chair"
	u"kɛnca",	#"contract"
	u"kɛmbo",	#"headman"
	u"keɣöö",	#"head monk"
	u"kerβa",	#"aristrocrat"
	u"qo",	#"head"
	u"qomba",	#"monastery"
	u"qɔr",	#"coat"
	u"qɔɔɔɔ",	#"round"
	u"č^hea",	#"half"
	u"č^huɣum",	#"cheese"
	u"topcaa",	#"stairs"
	u"t^hoõõ",	#"tonight"
	u"ṭaaãã",	#"post office"
	u"ṭuɣɨ",	#"harbor"
	u"ṭuNGo",	#"China"
	u"nɛNGaa",	#"important"
	u"paNGɔɔ",	#"chest"
	u"pɛɛβãã",	#"frog"
	u"simGãã", #"build a house"
        ],
    {"alternations": [{u"q": u"k",
                       u"G": u"g",
                       u"N": u"ŋ"},
                      {u"b": u"p",
                       u"g": u"k",
                       u"d": u"t",
                       u"ḍ": u"ṭ"}]}))


# Chapter 4
underlyingProblems = []
underlyingProblems.append(Problem(
    u'''
1. Axininca Campa
	Provide underlying representations and a phonological rule which will account for the following alternations.
    Output of system:
Phonological rules:
p ---> w / [  ] _ 
k ---> y / [  ] _ 
    ''',
    [(u"toniro",	u"notoniroti"),
     (u"yaarato",	u"noyaaratoti"),
     (u"kanari",	u"noyanariti"),
     (u"kosiri",	u"noyosiriti"),
     (u"pisiro",	u"nowisiroti"),
     (u"porita",	u"noworitati")
    ],
    solutions = [
        '''
 + stem + 
no + stem + ti
p > w / V_V
k > y / V_V
        ''']))

underlyingProblems.append(Problem(
    u'''
2. Kikuyu
	What is the underlying form of the infinitive prefix in Kikuyu? Give a rule that explains the non-underlying pronunciation of the prefix.
    ''',
    [(u"ɣotɛŋɛra",),
     (u"ɣokuua",),
     (u"ɣokoora",),
     (u"koruɣa",),
     (u"kooria",),
     (u"komɛɲa",),
     (u"kohɔta",),
     (u"ɣočina",),
     (u"koɣeera",),
     (u"koina",),
     (u"ɣočuuka",),
     (u"ɣokaya",),
     (u"koɣaya",)],
    solutions = [u'''
ko + stem + a
    k ---> ɣ / # _ V [ -continuant -sonorant ]
''']))

underlyingProblems.append(Problem(
    u'''
3: Korean
	Give the underlying representations of each of the verb stems found below; state what phonological rule applies to these data. [Note: there is a vowel harmony rule which explains the variation between final a and ə in the imperative, which you do not need to be concerned with]
    ''',
    [(u"ipə",		u"ipko"),
     (u"kupə",		u"kupko"),
     (u"kap^ha",		u"kapko"),
     (u"cip^hə",		u"cipko"),
     (u"tata",		u"tatko"),
     (u"put^hə",		u"putko"),
     (u"məkə",		u"məkko"),
     (u"čukə",		u"čukko"),
     (u"ikə",		u"ikko"),
     (u"taka",		u"takko"),
     (u"kaka", u"kakko"),
     (u"səkə",		u"səkko")],
    solutions = [u'''
 + stem + ə
 + stem + ko
    [ +aspirated ] > [ -aspirated ] / _ C
    ə > a / a C* _
''']))

underlyingProblems.append(Problem(
    '''
    Samoan
example from the textbook.
(problem 10)
    ''',
    [
        (u"olo", u"oloia"),
        (u"lafo",u"lafoia"),
        (u"usu",u"usuia"),
        (u"tau",u"tauia"),
        (u"taui",u"tauia"),
        (u"lele",u"lelea"),
        (u"tafe",u"tafea"),
        (u"tau",u"taulia"),
        (u"oso",u"osofia"),
        (u"valu",u"valusia"),
        (u"u:",u"u:tia")
    ],
    solutions = [u'''
 + stem + 
 + stem + ia
[ -vowel ] ---> Ø /  _ #
i ---> Ø / [ +vowel -back ] _ 
''']))

underlyingProblems.append(Problem(
    '''
    Russian
 devoicing of word final obscurant
(problem 11)
    ''',
    [
        (u"vagon", u"vagona"),
        (u"glas", u"glaza"),
        (u"golos",u"golosa"),
        (u"ras", u"raza"),
        (u"les",u"lesa"),
        (u"porok",u"poroga"),
        (u"vrak",u"vraga"),
        (u"urok",u"uroka"),
        (u"tvet",u"tveta"),
        (u"prut",u"pruda"),
        (u"soldat",u"soldata"),
        (u"zavot",u"zavoda"),
        (u"xlep",u"xleba"),
        (u"grip",u"griba"),
        (u"trup",u"trupa")
    ],
    solutions = [u'''
 + stem + 
 + stem + a
    [-sonorant] > [-voice] / _#''']))

underlyingProblems.append(Problem(
    '''
    English 
verb inflections.
(problem 12)
    ''',
    
    [(u"ro",u"rod",u"roz",u"roɩŋ"),
     (u"šo",u"šod",u"šoz",u"šoɩŋ"),
     (u"cal",u"cald",u"calz",u"calɩŋ"),
     (u"trn",u"trnd",u"trnz",u"trnɩŋ"),
     (u"græb",u"græbd",u"græbz",u"græbɩŋ"),
     (u"sim",u"simd",u"simz",u"simɩŋ"),
     (u"liv",u"livd",u"livz",u"livɩŋ"),
     (u"mʊv",u"mʊvd",u"mʊvz",u"mʊvɩŋ"),
     (u"həg",u"həgd",u"həgz",u"həgɩŋ"),
     (u"lʊk",u"lʊkt",u"lʊks",u"lʊkɩŋ"),
     (u"æsk",u"æskt",u"æsks",u"æskɩŋ"),
     (u"æsk",u"æskt",u"æsks",u"æskɩŋ"),
     (u"wɛrk",u"wɛrkt",u"wɛrks",u"wɛrkɩŋ"),
     (u"kɩs",u"kɩst",u"kɩsəz",u"kɩsɩŋ"),
     (u"fɩš",u"fɩšt",u"fɩšəz",u"fɩšɩŋ"),
     (u"kwɩz",u"kwɩzd",u"kwɩzəz",u"kwɩzɩŋ"),
     (u"bʌz",u"bʌzd",u"bʌzəz",u"bʌzɩŋ"),
     (u"wet",u"wetəd",u"wets",u"wetɩŋ"),
     (u"wed",u"wedəd",u"wedz",u"wedɩŋ"),
     (u"nid",u"nidəd",u"nidz",u"nidɩŋ"),
     (u"lɩft",u"lɩftəd",u"lɩfts",u"lɩftɩŋ")
     ],
    solutions = [u'''
 + stem + 
 + stem + d
 + stem + z
    0 > ə / [-continuant -sonorant +coronal] _ d#
    0 > ə / [+sibilant] _ z#
    d > [-voice] / [-voice]_#
    z > [-voice] / [-voice]_#''']))

underlyingProblems.append(Problem(
    u'''
4: Hungarian
	Explain what phonological process affects consonants in the following data (a vowel harmony rule makes suffix vowels back after back vowels and front after front vowels, which you do not need to account for). State what the underlying forms are for all morphemes.
    ''',
#	noun	in N	from N	to N	gloss
    [
	(u"kalap",	u"kalabban",	u"kalapto:l",	u"kalapnak"), #	hat
	(u"ku:t",	u"ku:dban",	u"ku:tto:l",	u"ku:tnak"), #	well
	(u"ža:k",	u"ža:gban",	u"ža:kto:l",	u"ža:knak"), #	sack
	(u"re:s",	u"re:zben",	u"re:stö:l",	u"re:snek"), #	part
	(u"šro:f ",	u"šro:vban ",	u"šro:fto:l ",	u"šro:fnak"), #	screw
	(u"laka:š",	u"laka:žban",	u"laka:što:l",	u"laka:šnak"), #	apartment
	(u"ketret^s",	u"ketred^zben",	u"ketret^stö:l",	u"ketret^snek"), #	cage
	(u"test",	u"tezdben",	u"testtö:l",	u"testnek"), #	body
	(u"rab",	u"rabban",	u"rapto:l",	u"rabnak"), #	prisoner
	(u"ka:d",	u"ka:dban",	u"ka:tto:l",	u"ka:dnak"), #	tub
	(u"meleg",	u"melegben",	u"melektö:l",	u"melegnek"), #	warm
	(u"vi:z",	u"vi:zben",	u"vi:stö:l",	u"vi:znek"), #	water
	(u"vara:ž",	u"vara:žban",	u"vara:što:l",	u"vara:žnak"), #	magic
	(u"a:g^y",	u"a:g^yban",	u"a:k^yto:l",	u"a:g^ynak"), #	bed
	(u"sem",	u"semben",	u"semtö:l",	u"semnek"), #	eye
	(u"bün",	u"bünben",	u"büntö:l",	u"bünnek"), #	crime
	(u"toroñ",	u"toroñban",	u"toroñto:l",	u"toroñnak"), #	tower
	(u"fal",	u"falban",	u"falto:l",	u"falnak"), #	wall
	(u"ö:r",	u"ö:rben",	u"ö:rtö:l",	u"ö:rnek"), #	guard
	(u"sa:y",	u"sa:yban",	u"sa:yto:l",	u"sa:ynak") #	mouth
    ],
    solutions = [
        u'''
 + stem + 
 + stem + ban
 + stem + to:l
 + stem + nak
        [+vowel] > [-back -low] / [+vowel -back ] [ ]* _
        [ -sonorant ] > [+voice] / _ b
        [ -sonorant ] > [-voice] / _[-voice]
        ''']))

underlyingProblems.append(Problem(
    u'''
5: Kikuria
	Provide appropriate underlying representations and phonological rules which will account for the following data.
    ''',
	#verb	verb for
	[
            (u"suraaŋga",	u"suraaŋgera"), #	‘praise’
	    (u"taaŋgata",	u"taaŋgatera"), #	‘lead’
	    (u"baamba",	u"baambera"), #	‘fit a drum head’
	    (u"reenda",	u"reendera"), #	‘guard’
	    (u"rema",	u"remera"), #	‘cultivate’	
	    (u"hoora",	u"hoorera"), #	‘thresh’	
	    (u"roma",	u"romera"), #	‘bite’	
	    (u"sooka",	u"sookera"), #	‘respect’	
	    (u"tačora",	u"tačorera"), #	‘tear’
	    (u"siika",	u"seekera"), #	‘close’
	    (u"tiga",	u"tegera"), #	‘leave behind’
	    (u"ruga",	u"rogera"), #	‘cook’
	    (u"suka",	u"sokera"), #	‘plait’
	    (u"huuta",	u"hootera"), #	‘blow’
	    (u"riiŋga",	u"reeŋgera"), #	‘fold’
	    (u"siinda",	u"seendera")],
    solutions = [u'''
 + stem + a
 + stem + era
    V > [-high]/_[ -liquid ]* e
'''])) #	‘win’

underlyingProblems.append(Problem(
    u'''
6: Farsi
Give the underlying forms for the following nouns, and say what phonological rule is necessary to explain the following data.
    ''',
	#singular	plural	gloss
    [
	(u"zæn",	u"zænan"), #	woman
	(u"læb",	u"læban"), #	lip
	(u"hæsud",	u"hæsudan"), #	envious
	(u"bæradær",	u"bæradæran"), #	brother
	(u"bozorg",	u"bozorgan"), #	big
	(u"mæleke",	u"mælekean"), #	queen
	(u"valede",	u"valedean"), #	mother
	(u"kæbire",	u"kæbirean"), #	big
	(u"ahu",	u"ahuan"), #	gazelle
	(u"hamele",	u"hamelean"), #	pregnant
	(u"bačče",	u"baččegan"), #	child
	(u"setare",	u"setaregan"), #	star
	(u"bænde",	u"bændegan"), #	slave
	(u"azade",	u"azadegan"), #	freeborn
	(u"divane",	u"divanegan")], #	insane
    solutions = [u'''
 + stem + 
 + stem + an
g ---> 0 / e _ #''']))

underlyingProblems.append(Problem(
    u'''7: Tibetan
Numbers between 11 and 19 are formed by placing the appropriate digit after the number 10, and multiples of 10 are formed by placing the appropriate multiplier before the number 10. What are the underlying forms of the basic numerals, and what phonological rule is involved in accounting for these data?
    ''',
    [
	u"ǰu",#	‘10’
	u"ǰig",#	‘1’
        u"ǰugǰig",#	‘11’
	u"ši",#	‘4’
	u"ǰubši",#	‘14’
        u"šibǰu",#	‘40’
	u"gu",#	‘9’
	u"ǰurgu",#	‘19’
	u"gubǰu",#	‘90’
	u"ŋa",#	‘5’
	u"ǰuŋa",#	‘15’
	u"ŋabǰu"],#	‘50’
    parameters = [10,1,11,4,14,40,9,19,90,5,15,50],
    solutions = [u'''
C > 0/#_C''']))

underlyingProblems.append(Problem(
    u'''
8: Makonde
Explain what phonological rules apply in the following examples (the acute accent in these example marks stress, whose position is predictable).
    ''',
	#repeated	past		imperative	gloss
	#imperative
    [
	(u"amáŋga",	u"amíle",		u"áma"),#		move
	(u"taváŋga",	u"tavíle",		u"táva"),#		wrap
	(u"akáŋga",		u"akíle",		u"áka"),#		hunt
	(u"patáŋga",	u"patíle",		u"póta"),#		twist
	(u"tatáŋga",		u"tatíle",		u"tóta"),#		sew
	(u"dabáŋga",	u"dabíle",		u"dóba"),#		get tired
	(u"aváŋga",		u"avíle",		u"óva"),#		miss
	(u"amáŋga",	u"amíle",		u"óma"),#		pierce
	(u"tapáŋga",	u"tapíle",		u"tépa"),#		bend
	(u"patáŋga",	u"patíle",		u"péta"),#		separate
	(u"aváŋga",		u"avíle",		u"éva"),#		separate
	(u"babáŋga",	u"babíle",		u"béba"),#		hold like a baby
	(u"utáŋga",		u"utíle",		u"úta"),#		smoke
	(u"lukáŋga",	u"lukíle",		u"lúka"),#		plait
	(u"lumáŋga",	u"lumíle",		u"lúma"),#		bite
	(u"uŋgáŋga",	u"uŋgíle",		u"úŋga"),#		tie
	(u"iváŋga",		u"ivíle",		u"íva"),#		steal
	(u"pitáŋga",		u"pitíle",		u"píta"),#		pass
	(u"imbáŋga",	u"imbíle",		u"ímba"),#		dig
	(u"limáŋga",	u"limíle",		u"líma")],#		cultivate
    solutions = [u'''
 + stem + á ŋ g a
 + stem + í l e
 + stem + a
[ +vowel ] ---> [ +highTone ] /  _ C* a
[ +highTone ] ---> a /  _ [  ] [ +highTone ]
''']))

underlyingProblems.append(Problem(
    u'''
9: North Saami
Posit appropriate underlying forms and any rules needed to explain the following alternations. The emphasis heret should be on correctly identifying the underlying form: the exact nature of the changes seen here is a more advanced problem.
    My analysis:
    {h,g,b,ð} > t / _ #
    {ǰ} > š / _ #
    m > n / _ #
    Not affected: s
    ''',
	#Nominative sg.	Essive
    [
	(u"varit",	u"varihin"),#	“2 year old reindeer buck”
	(u"oahpis",	u"oahpisin"),#	“acquaintance”
	(u"čoarvuš",	u"čoarvušin"),#	“antlers & skullcap”
	(u"lottaaš",	u"lottaaǰin"),#	“small bird”
	(u"čuoivvat",	u"čuoivvagin"),#	“yellow-brown reindeer”
	(u"ahhkut",	u"ahhkubin"),#	“grandchild of woman”
	(u"suohkat",	u"suohkaðin"),#	“thick”
	(u"heeǰoš",	u"heeǰoǰin"),#	“poor guy”
	(u"aaǰǰut",	u"aaǰǰubin"),#	“grandchild of man”
	(u"bissobeahtset",	u"bissobeahtsehin"),#	“butt of gun”
	(u"čeahtsit",	u"čeahtsibin"),#	“children of elder brother of man”
	(u"yaaʔmin",	u"yaaʔmimin"),#	“death”
	(u"čuoivat",	u"čuoivagin"),#	“yellow-grey reindeer”
	(u"laageš",	u"laageǰin"),#	“mountain birch”
	(u"gahpir",	u"gahpirin"),#	“cap”
	(u"gaauhtsis",	u"gaauhtsisin"),#	“8 people”
	(u"aaslat",	u"aaslagin"),#	man’s name
	(u"baðoošgaattset",	u"baðoošgaattsebin"),#	“bird type”
	(u"ahhkit",	u"ahhkiðin"),#	“boring”
	(u"bahaanaalat",	u"bahaanaalagin"),#	“badly behaved”
	(u"beštor",	u"beštorin"),#	“bird type”
	(u"heevemeahhtun",	u"heevemeahhtunin"),#	“inappropriate”
	(u"beeǰot",	u"beeǰohin"),#	“white reindeer”
	(u"bissomeahtun",	u"bissomeahtumin"),#	“unstable”
	(u"laðas",	u"laðasin"),#	“something jointed”
	(u"heaiyusmielat",	u"heaiyusmielagin"),#	“unhappy”
	(u"heaŋkkan",	u"heaŋkkanin"),#	“hanger”
	(u"yaman",	u"yamanin")],#	“something that makes noise”
    solutions = [u'''
 + stem + 
 + stem + in
m > n/_#
[-sibilant -nasal -liquid] ---> t /  _ #
ǰ ---> š /  _ #''']))



underlyingProblems.append(Problem(
    '''
    Finnish
 nominative versus positive.
(problem 13)
    ''',
    [(u"aamu",u"aamua"),
     (u"hopea",u"hopeaa"),
     (u"katto",u"kattoa"),
     (u"kello",u"kelloa"),
#     (u"kirya",u"kiryaa"), # I think this is a typo in the textbook
     (u"külmæ",u"külmææ"),
     (u"koulu",u"koulua"),
     (u"lintu",u"lintua"),
     (u"hüllü",u"hüllüæ"),
     (u"kömpelö",u"kömpelöæ"),
     (u"nækö",u"næköæ"),
     (u"yoki",u"yokea"),
     (u"kivi",u"kiveæ"),
     (u"muuri",u"muuria"),
     (u"naapuri",u"naapuria"),
     (u"nimi",u"nimeæ"),
#      (u"kaappi",u"kaappia"), # this was also be a typo: inconsistent with textbook solution
     #     (u"kaikki",u"kaikkea"), # oh I think I see what's going on: APA [a] is ambiguous
     (u"kiirehti",u"kiirehtiæ")],
    solutions = [u'''
 + stem + 
 + stem + æ
æ > a / [+back +vowel] [ ]* _ #
    e > i / _ #''']))

underlyingProblems.append(Problem(
    '''
    Lithuanian 
voicing assimilation & epenthesis
(problem 14)
todo: not enough data for it to get this one
    ''',
    [(u"ateiti",),
     (u"atimti",),
     (u"atleisti",),
     (u"atlikti",),
     (u"atko:pti",),
     (u"atkurti",),
     (u"adbekti",),
     (u"adgauti",),
     (u"adbukti",),
     (u"adgimti",),
     (u"atiduoti",),
     (u"atidari:ti",),
     (u"atideti",),
     (u"atiteisti",),],
    solutions = [u'''
at + stem + ti
    0 > i/ [+stop +coronal] _ [+stop +coronal]
    [-sonorant] > [+voice]/_[+voice -sonorant]
''']))

underlyingProblems.append(Problem(
    '''
    Armenian 
voicing assimilation & epenthesis
(problem 15)
todo: not enough data for it to get this one
    ''',
    [(u"kert^ham",),
     (u"kasiem",),
     (u"kaniem",),
     (u"kakaniem",),
     (u"kurriem",),
     (u"kətam",),
     (u"kəkienam",),
     (u"gəbəzzam",),
     (u"gəlam",)],
    solutions = [u'''
k + stem + am
a > e/i_
    [-sonorant] > [+voice]/_[+voice -vowel]
    0 > ə / [-anterior +stop]_C
''']))

# underlyingProblems.append(Problem(
#     u'''
#     (adapted from 9): North Saami, but only with the m/n alternation included
# Posit appropriate underlying forms and any rules needed to explain the following alternations. The emphasis heret should be on correctly identifying the underlying form: the exact nature of the changes seen here is a more advanced problem.
#     My analysis:
#     {h,g,b,ð} > t / _ #
#     {ǰ} > š / _ #
#     m > n / _ #
#     Not affected: s
#     ''',
# 	#Nominative sg.	Essive
#     [
# #	(u"varit",	u"varihin"),#	“2 year old reindeer buck”
# 	(u"oahpis",	u"oahpisin"),#	“acquaintance”
# 	(u"čoarvuš",	u"čoarvušin"),#	“antlers & skullcap”
# #	(u"lottaaš",	u"lottaaǰin"),#	“small bird”
# #	(u"čuoivvat",	u"čuoivvagin"),#	“yellow-brown reindeer”
# #	(u"ahhkut",	u"ahhkubin"),#	“grandchild of woman”
# #	(u"suohkat",	u"suohkaðin"),#	“thick”
# #	(u"heeǰoš",	u"heeǰoǰin"),#	“poor guy”
# #	(u"aaǰǰut",	u"aaǰǰubin"),#	“grandchild of man”
# #	(u"bissobeahtset",	u"bissobeahtsehin"),#	“butt of gun”
# #	(u"čeahtsit",	u"čeahtsibin"),#	“children of elder brother of man”
# 	(u"yaaʔmin",	u"yaaʔmimin"),#	“death”
# #	(u"čuoivat",	u"čuoivagin"),#	“yellow-grey reindeer”
# #	(u"laageš",	u"laageǰin"),#	“mountain birch”
# #	(u"gahpir",	u"gahpirin"),#	“cap”
# 	(u"gaauhtsis",	u"gaauhtsisin"),#	“8 people”
# #	(u"aaslat",	u"aaslagin"),#	man’s name
# #	(u"baðoošgaattset",	u"baðoošgaattsebin"),#	“bird type”
# #	(u"ahhkit",	u"ahhkiðin"),#	“boring”
# #	(u"bahaanaalat",	u"bahaanaalagin"),#	“badly behaved”
# 	(u"beštor",	u"beštorin"),#	“bird type”
# 	(u"heevemeahhtun",	u"heevemeahhtunin"),#	“inappropriate”
# #	(u"beeǰot",	u"beeǰohin"),#	“white reindeer”
# 	(u"bissomeahtun",	u"bissomeahtumin"),#	“unstable”
# 	(u"laðas",	u"laðasin"),#	“something jointed”
# #	(u"heaiyusmielat",	u"heaiyusmielagin"),#	“unhappy”
# 	(u"heaŋkkan",	u"heaŋkkanin"),#	“hanger”
# 	(u"yaman",	u"yamanin")]))

# underlyingProblems.append(Problem(
#     '''deGemini test''',
#     [(u"tes",u"tessi"),
#      (u"tes",u"tesi"),
#      (u"ak",u"akki"),
#      (u"lof",u"loffi"),
#      (u"pig",u"pigi")]))

interactingProblems = []

interactingProblems.append(Problem(
    '''1: Kerewe

What two tone rules are motivated by the following data; explain what order the rules apply in.
    ''',
    #to V	to V e.o	to V for	to V for e.o	to V us		to V it		to V for us	to V it for us
	[
            (u"kubala",	u"kubalana",	u"kubalila",	u"kubalilana", u"kutúbála",	u"kukíbála",	u"kutúbálila",	u"kukítúbalila"),#	“count”
	    (u"kugaya",	u"kugayana",	u"kugayila",	u"kugayilana", u"kutúgáya",	u"kukígáya",	u"kutúgáyila",	u"kukítúgayila"),#	“despise”
	    (u"kugula",	u"kugulana",	u"kugulila",	u"kugulilana", u"kutúgúla",	u"kukígúla",	u"kutúgúlila",	u"kukítúgulila"),#	“buy”
	    (u"kubála",	u"kubálána",	u"kubálíla",	u"kubálílana", u"kutúbála",	u"kukíbála",	u"kutúbálila",	u"kukítúbalila"),#	“kick”
	    (u"kulúma",	u"kulúmána",	u"kulúmíla",	u"kulúmílana", u"kutúlúma",	u"kukílúma",	u"kutúlúmila",	u"kukítúlumila"),#	“bite” suffices to trigger the bug
	    (u"kusúna",	u"kusúnána",	u"kusúníla",	u"kusúnílana", u"kutúsúna",	u"kukísúna",	u"kutúsúnila",	u"kukítúsunila"),#	“pinch”
	    (u"kulába",	u"kulábána",	u"kulábíla",	u"kulábílana", u"kutúlába",	u"kukílába",	u"kutúlábila",	u"kukítúlabila")#	“pass”
        ],
    solutions = [u'''
	 k u  + stem +  a 
	 k u  + stem +  a n a 
	 k u  + stem +  i l a 
	 k u  + stem +  i l a n a 
	 k u t ú  + stem +  a 
	 k u k í  + stem +  a 
	 k u t ú  + stem +  i l a 
	 k u k í t ú  + stem +  i l a 
[  ] ---> [ -highTone ] / [ +highTone ] [  ] _ 
[  ] ---> [ +highTone ] / [ +highTone ] [  ] _ [  ]
''']))

interactingProblems.append(Problem(
    '''2: Polish

What phonological rules are motivated by the following examples, and what order do those rules apply in?
''',
    #singular	plural		singular	plural
	[
            (u"klup",	u"klubi"),#	‘club’
            (u"trup",	u"trupi"),#	‘corpse’
	    (u"dom",	u"domi"),#	‘house’
            (u"snop",	u"snopi"),#	‘sheaf’
	    (u"žwup",	u"žwobi"),#	‘crib’
            (u"trut",	u"trudi"),#	‘labor’
	    (u"dzvon",	u"dzvoni"),#	‘bell’
            (u"kot",	u"koti"),#	‘cat’
	    (u"lut",	u"lodi"),#	‘ice’
            (u"grus",	u"gruzi"),#	‘rubble’
	    (u"nos",	u"nosi"),#	‘nose’
            (u"vus",	u"vozi"),#	‘cart’
	    (u"wuk",	u"wugi"),#	‘lye’
            (u"wuk",	u"wuki"),#	‘bow’
	    (u"sok",	u"soki"),#	‘juice’
            (u"ruk",	u"rogi"),#	‘horn’
	    (u"bur",	u"bori"),#	‘forest’
            (u"vuw",	u"vowi"),#	‘ox’
	    (u"sul",	u"soli"),#	‘salt’
            (u"buy",	u"boyi"),#	‘fight’
	    (u"šum",	u"šumi"),#	‘noise’
            (u"žur",	u"žuri")],#	‘soup’
    solutions = [u'''
 + stem + 
 + stem + i
o ---> u /  _ [ -nasal +voice ] #
[ -sonorant ] ---> [ -voice ] /  _ #
''']))

interactingProblems.append(Problem(
    '''3: Ancient Greek

Discuss the phonological rules and underlying representations which are necessary to account for the following nouns; comment on the ordering of these phonological processes.

Greedy search discovers
    [ -sonorant ] ---> [ -aspirated -voice ] /  _ [ -voice ]
    So we unaspirate whenever the next sound is unvoiced, which bizarrely seems to work.
    obstructions also become you voiced whenever the next sound is unvoiced
it also looks like coronal is deleted in certain contexts.
    deleted after /s/?
    deleted: {t,d,n} / _ s
    ''',
#	nom. sg.	gen. sg.	dat. sg	dat. pl.
    [
	(u"hals",	u"halos",	u"hali",	u"halsi"),#	‘salt’
	(u"oys",	u"oyos",	u"oyi",	u"oysi"),#	‘sheep’
	(u"sus",	u"suos",	u"sui",	u"susi"),#	‘sow’
	(u"klo:ps",	u"klo:pos",	u"klo:pi",	u"klo:psi"),#	‘thief’
	(u"p^hle:ps",	u"p^hle:bos",	u"p^hle:bi",	u"p^hle:psi"),#	‘vein’
	(u"kate:lips",	u"kate:lip^hos",	u"kate:lip^hi",	u"kate:lipsi"),#	‘upper story’
	(u"p^hulaks",	u"p^hulakos",	u"p^hulaki",	u"p^hulaksi"),#	‘guard’
	(u"ayks",	u"aygos",	u"aygi",	u"ayksi"),#	‘goat’
	(u"salpiŋks",	u"salpiŋgos",	u"salpiŋgi",	u"salpiŋksi"),#	‘trumpet’
	(u"onuks",	u"onuk^hos",	u"onuk^hi",	u"onuksi"),#	‘nail’
	(u"t^he:s",	u"t^he:tos ",	u"t^he:ti ",	u"t^he:si"),#	‘serf’
	(u"k^haris",	u"k^haritos",	u"k^hariti",	u"k^harisi"),#	‘grace’
	(u"elpis",	u"elpidos",	u"elpidi",	u"elpisi"),#	‘hope’
	(u"korus",	u"korut^hos",	u"korut^hi",	u"korusi"),#	‘helmet’
	(u"ri:s",	u"ri:nos",	u"ri:ni",	u"ri:si"),#	‘nose’
	(u"delp^hi:s",	u"delp^hi:nos",	u"delp^hi:ni",	u"delp^hi:si")],#	‘porpoise’
    solutions = [u'''
 + stem + s
 + stem + os
 + stem + i
 + stem + si
[ -sonorant ] ---> [ -voice ] /  _ [ -voice ]
[ -sonorant ] ---> [ -aspirated ] /  _ [ -voice ]
[ +coronal -liquid ] > 0 / _ s
''']))

interactingProblems.append(
Problem(
u'''4: Shona
	Acute accent indicates H tone and unaccented vowels have L tone. Given the two sets of data immediately below, what tone rule do the following data motivate? There are alternations in the form of adjectives, e.g. kurefú, karefú, marefú all meaning “long”. Adjectives have an agreement prefix, hence ku-refú marks the form of the adjective in one grammatical class, and so on. In some cases, the agreement is realized purely as a change in the initial consonant of the adjective, i.e. gúrú ~ kúrú ~ húrú which need not be explained.
''',
    stripConsonants(processMorphology(
        ['baboon',
         'boy (aug.)',
         'table',
         'word',
         'hoe',
         'house',
         'gazelle',
         'money',
         'knife',
         'axe',
         'messenger',
         'cloth',
         'pot',
         'worms',
         'wealth',
         'country',
         'bones',
         'pumpkin',
         'porcupine',
         'firewood',
         'books',
         'book',
         'store',
         'baboons',
         'hoes',
         'knives',
         'words',
         'axes',
         'to the land',
         'gazelle (dim.)',
         'porcupines (dim.)',
         'letter',
         'person',
         'clothes'],
        ['',
         'died',
         'big',
         'bigp',
         'short',
         'shortp',
         'clean',
         'fell',
         'many',
         'tall',
         'long',
         'longp',
         'thick',
         'thickp',
         'thin',
         'short2',
         'thin2'],
        {
	u'bveni':	'baboon',	u'bveni pfúpi':	'short baboon',
	u'guɗo':	'baboon',	u'gudo rákafá':	'baboon died',
        u'táfura':	'table',	u'táfura húrú':	'big table',
	u'šoko':	'word',	u'šoko bvúpi':	'short word',
	u'ɓadzá':	'hoe',	u'ɓadzá gúrú':	'big hoe',
	u'zigómaná':	'boy (aug.)',	u'zigómaná gúrú':	'big boy (aug.)',
	u'imbá':	'house',	u'imbá čéna':	'clean house',
	u'mhará':	'gazelle',	u'mhará čéna':	'clean gazelle',
	u'marí':	'money',	u'marí čéna':	'clean money',

	u'ɓáŋgá':	'knife',	u'ɓáŋga gúrú':	'big knife',
	u'ɗémó':	'axe',	u'ɗémo bvúpi':	'short axe',
	u'nhúmé':	'messenger',	u'nhúme pfúpi':	'short messenger',
	u'ǰírá':	'cloth',	u'ǰíra ǰéna':	'clean cloth',
	u'hárí':	'pot',	u'hári húrú':	'big pot',
	u'mbúndúdzí':	'worms',	u'mbúndúdzi húrú':	'big worms',
	u'fúma':	'wealth',	u'fúma čéna':	'clean wealth',
	u'nyíka':	'country',	u'nyíka húrú':	'big country',
	u'hákáta':	'bones',	u'hákáta pfúpi':	'short bones',
	u'ǰékéra':	'pumpkin',	u'ǰékéra gúrú':	'big pumpkin',

#These data provide further illustration of the operation of this tone rule, which will help you to state the conditions on the rule correctly.


	#u'ɓadzá':	'hoe',
	    u'ɓadzá rákawá':	'hoe fell',
	u'nuŋgú':	'porcupine',	u'nuŋgú yákafá':	'porcupine died',
	#u'ɓáŋgá':	'knife',
            u'ɓáŋga rákawá':	'knife fell',
	u'nhúmé':	'messenger',
	    u'nhúme yákafá':	'messenger died',
	u'búku':	'book',	u'búku rákawá':	'book fell',
	u'mapfeni':	'baboons',	u'mapfeni makúrú':	'bigp baboons',
	u'mapadzá':	'hoes',	u'mapadzá makúrú':	'bigp hoes',
	u'mapáŋgá':	'knives',	u'mapáŋgá makúrú':	'bigp knives',
	u'nhúmé':	'messenger',	u'nhúmé ndefú':	'short2 messenger',
	u'matémó':	'axes',	u'matémó mapfúpi':	'shortp axes',
	u'mabúku':	'books',	u'mabúku mažínǰí':	'many books',
	u'čitóro':	'store',	u'čitóro čikúrú':	'bigp store',

	#In the examples below, a second tone rule applies.

	u'guɗo':	'baboon',	u'guɗo refú':	'tall baboon',
	u'búku':	'book',	u'búku refú':	'long book',
	u'ɓadzá':	'hoe',	u'ɓadzá refú':	'long hoe',
	u'nuŋgú':	'porcupine',	u'nuŋgú ndefú':	'long porcupine',
	u'mašoko':	'words',	u'mašoko marefú':	'longp words',
	u'kunyíka':	'to the land',	u'kunyíka kurefú':	'longp to the land',
	u'mapadzá':	'hoes',	u'mapadzá márefú':	'longp hoes',
	u'kamhará':	'gazelle (dim.)',	u'kamhará kárefú':	'longp gazelle (dim.)',
	u'tunuŋgú':	'porcupines (dim.)',	u'tunuŋgú túrefú':	'longp porcupines (dim.)',

	u'guɗo':	'baboon',	u'guɗo gobvú':	'thick baboon',
	u'búku':	'book',	u'búku gobvú':	'thick book',
	u'ɓadzá':	'hoe',	u'ɓadzá gobvú':	'thick hoe',
	u'makuɗo':	'baboons',	u'makuɗo makobvú':	'thickp baboons',
	u'mapadzá':	'hoes',	u'mapadzá mákobvú':	'thickp hoes',
	u'tsamba':	'letter',	u'tsamba nhete':	'thin letter',
	u'búku':	'book',	u'búku ɗete':	'thin book',
	u'ɓadzá':	'hoe',	u'badzá ɗéte':	'thin hoe',
	u'imbá':	'house',	u'imbá nhéte':	'thin house',

#	What do the following examples show about these tone rules?

	u'ɓáŋgá':	'knife',	u'ɓáŋgá ɗéte':	'thin knife',
	u'ɗémó':	'axe',	u'ɗémó ɗéte':	'thin axe',
	u'murúmé':	'person',	u'murúmé mútete':	'thin2 person',
	u'kahúní':	'firewood',	u'kahúní kárefú':	'longp firewood',
	u'mačírá':	'clothes',	u'mačírá márefú':	'longp clothes',
	    u'hárí':	'pot',	u'hárí nhéte':	'thin pot'})),
    solutions=[u'''
 + stem + 
 + stem + ##áaá ; died
 + stem + ##áá ; big
 + stem + ##aáá ; bigp
 + stem + ##áa ; short
 + stem + ##aáa ; shortp
 + stem + ##áa ; clean
 + stem + ##áaá ; fell
 + stem + ##aáá ; many
 + stem + ##aá ; tall
 + stem + ##aá ; long
 + stem + ##aaá ; longp
 + stem + ##aá ; thick
 + stem + ##aaá ; thickp
 + stem + ##aa ; thin
 + stem + ##aá ; short2
 + stem + ##aaa ; thin2
    V > [-highTone] / [+highTone]_ ## [+highTone]
    V > [+highTone] / [+highTone] ## _ [-highTone]
'''])
    )
# print unicode(interactingProblems[-1])
# assert False


interactingProblems.append(Problem(
'''5: Catalan

Give phonological rules which account for the following data, and indicate what ordering is necessary between these rules. For each adjective stem, state what the underlying form of the root is. Pay attention to the difference between surface [b,d,g] and [β,ð,ɣ], in terms of predictability.
NOTE: This problem set had a bug in it that Tim discovered.
/d/ is actually a dental in this language
So I have replaced it with /d/
/t/ might actually also be a dental
So I have replaced it with /t/
feminine suffix: ə
word final devoicing
in between sonants voiced fricatives become stops


''',		
#ma	masc	fem		masc	fem	
#	sing.	sing.		sing.	sing.
    [
	(u"əkely",	u"əkelyə"),#	‘that’
	(u"mal",	u"malə"),#	‘bad’
	(u"siβil",	u"siβilə"),#	‘civil’
	(u"əskerp",	u"əskerpə"),#	‘shy’
	(u"šop",	u"šopə"),#	‘drenched’
	(u"sɛk",	u"sɛkə"),#	‘dry’
	(u"əspɛs",	u"əspɛsə"),#	‘thick’
	(u"gros",	u"grosə"),#	‘large’
	(u"baš",	u"bašə"),#	‘short’
	(u"koš",	u"košə"),#	‘lame’
	(u"tot",	u"totə"),#	‘all’
	(u"brut",	u"brutə"),#	‘dirty’
	(u"pɔk",	u"pɔkə"),#	‘little’
	(u"prəsis",	u"prəsizə"),#	‘precise’
	(u"frənses",	u"frənsezə"),#	‘French’
	(u"gris",	u"grizə"),#	‘grey’
	(u"kəzat",	u"kəzaðə"),#	‘married’
	(u"bwit",	u"bwiðə"),#	‘empty’
	(u"rɔč",	u"rɔžə"),#	‘red’
	(u"boč",	u"božə"),#	‘crazy’
	(u"orp",	u"orβə"),#	‘blind’
	(u"lyark",	u"lyarɣə"),#	‘long’
	(u"sek",	u"seɣə"),#	‘blind’
	(u"fəšuk",	u"fəšuɣə"),#	‘heavy’
	(u"grok",	u"groɣə"),#	‘yellow’
	(u"puruk",	u"puruɣə"),#	‘fearful’
	(u"kandit",	u"kandiðə"),#	‘candid’
	(u"frɛt",	u"frɛðə"),#	‘cold’
	(u"səɣu",	u"səɣurə"),#	‘sure’
	(u"du",	u"durə"),#	‘hard’
	(u"səɣəðo",	u"səɣəðorə"),#	‘reaper’
	(u"kla",	u"klarə"),#	‘clear’
	(u"nu",	u"nuə"),#	‘nude’
	(u"kru",	u"kruə"),#	‘raw’
	(u"flɔñǰu",	u"flɔñǰə"),#	‘soft’
	(u"dropu",	u"dropə"),#	‘lazy’
	(u"əgzaktə",	u"əgzaktə"),#	‘exact’
	(u"əlβi",	u"əlβinə"),#	‘albino’
	(u"sa",	u"sanə"),#	‘healthy’
	(u"pla",	u"planə"),#	‘level’
	(u"bo",	u"bonə"),#	‘good’
	(u"sərɛ",	u"sərɛnə"),#	‘calm’
	(u"suβlim",	u"suβlimə"),#	‘sublime’
	(u"al",	u"altə"),#	‘tall’
	(u"fɔr",	u"fɔrtə"),#	‘strong’
	(u"kur",	u"kurtə"),#	‘short’
	(u"sor",	u"sorðə"),#	‘deaf’
	(u"bɛr",	u"bɛrðə"),#	‘green’
	(u"san",	u"santə"),#	‘saint’
	(u"kəlɛn",	u"kəlɛntə"),#	‘hot’
	(u"prufun",	u"prufundə"),#	‘deep’
	(u"fəkun",	u"fəkundə"),#	‘fertile’
	(u"dəsen",	u"dəsentə"),#	‘decent’
	(u"dulen",	u"dulentə"),#	‘bad’
	(u"əstuðian",	u"əstuðiantə"),#	‘student’
	(u"blaŋ",	u"blaŋkə")],#	‘white’
    solutions = [u''' + stem + 
 + stem + ə
    [-sonorant] > [-voice] / _ #
    [-sonorant +voice] > [+continuant] / [+sonorant -nasal] _ [+sonorant]
    [+sonorant -lateral +coronal] > 0 / _ #
    [+coronal -sonorant] > 0 / [+coronal +sonorant] _ #
    k > 0 /  ŋ _ #
    [+vowel] > 0 / [+vowel] [-vowel]* _ [+vowel] #''']))

interactingProblems.append(Problem(
    '''6: Finnish
Propose rules which will account for the following alternations. It would be best not to write a lot of rules which go directly from underlying forms to surface forms in one step; instead, propose a sequence of rules whose combined effect brings about the change in the underlying form. Pay attention to what consonants actually exist in the language.
    ''',
    [
	#genitive	nom.	nom.	ablative	essive	gloss
	#sing.	sing.	pl.	sing.	sing.	
	(u"kanadan",	u"kanada",	u"kanadat",	u"kanadalta",	u"kanadana"),#	Canada
	(u"kiryan",	u"kirya",	u"kiryat",	u"kiryalta",	u"kiryana"),#	book
	(u"aamun",	u"aamu",	u"aamut",	u"aamulta",	u"aamuna"),#	morning
	(u"talon",	u"talo",	u"talot",	u"talolta",	u"talona"),#	house
	(u"koiran",	u"koira",	u"koirat",	u"koiralta",	u"koirana"),#	dog
	(u"hüvæn",	u"hüvæ",	u"hüvæt",	u"hüvæltæ",	u"hüvænæ"),#	good
	(u"kuvan",	u"kuva",	u"kuvat",	u"kuvalta",	u"kuvana"),#	picture
	(u"lain",	u"laki",	u"lait",	u"lailta",	u"lakina"),#	roof
	(u"nælæn",	u"nælkæ",	u"nælæt",	u"nælæltæ",	u"nælkænæ"),#	hunger
	(u"yalan",	u"yalka",	u"yalat",	u"yalalta",	u"yalkana"),#	leg
	(u"leuan",	u"leuka",	u"leuat",	u"leualta",	u"leukana"),#	chin
	(u"paran",	u"parka",	u"parat",	u"paralta",	u"parkana"),#	poor
	(u"reiæn",	u"reikæ",	u"reiæt",	u"reiæltæ",	u"reikænæ"),#	hole
	(u"nahan",	u"nahka",	u"nahat",	u"nahalta",	u"nahkana"),#	hide
	(u"vihon",	u"vihko",	u"vihot",	u"viholta",	u"vihkona"),#	notebook
	(u"laihan",	u"laiha",	u"laihat",	u"laihalta",	u"laihana"),#	lean
	(u"avun",	u"apu",	u"avut",	u"avulta",	u"apuna"),#	help 
	(u"halvan",	u"halpa",	u"halvat",	u"halvalta",	u"halpana"),#	cheap
	(u"orvon",	u"orpo",	u"orvot",	u"orvolta",	u"orpona"),#	orphan
	(u"leivæn",	u"leipæ",	u"leivæt",	u"leivæltæ",	u"leipænæ"),#	bread
	(u"pæivæn",	u"pæivæ",	u"pæivæt ",	u"pæivæltæ ",	u"pæivænæ"),#	day
	(u"kilvan",	u"kilpa",	u"kilvat",	u"kilvalta",	u"kilpana"),#	competition
	(u"külvün",	u"külpü",	u"külvüt",	u"külvültæ",	u"külpünæ"),#	bath
	(u"tavan",	u"tapa",	u"tavat",	u"tavalta",	u"tapana"),#	manner
	(u"korvan",	u"korva",	u"korvat",	u"korvalta",	u"korvana"),#	ear
	(u"æidin",	u"æiti",	u"æidit",	u"æidiltæ",	u"æitinæ"),#	mother
	(u"kodin",	u"koti",	u"kodit",	u"kodilta",	u"kotina"),#	home
	(u"muodon",	u"muoto",	u"muodot",	u"muodolta",	u"muotona"),#	form
	(u"tædin",	u"tæti",	u"tædit",	u"tædiltæ",	u"tætinæ"),#	aunt
	(u"kadun",	u"katu",	u"kadut",	u"kadulta",	u"katuna"),#	street
	(u"maidon",	u"maito",	u"maidot",	u"maidolta",	u"maitona"),#	milk
	(u"pöüdæn",	u"pöütæ",	u"pöüdæt",	u"pöüdæltæ",	u"pöütænæ"),#	table
	(u"tehdün",	u"tehtü",	u"tehdüt",	u"tehdültæ",	u"tehtünæ"),#	made
	(u"læmmön",	u"læmpö",	u"læmmöt",	u"læmmöltæ",	u"læmpönæ"),#	warmth
	(u"laŋŋan",	u"laŋka",	u"laŋŋat",	u"laŋŋalta",	u"laŋkana"),#	thread
	(u"sæŋŋün",	u"sæŋkü",	u"sæŋŋüt",	u"sæŋŋültæ",	u"sæŋkünæ"),#	bed
	(u"hinnan",	u"hinta",	u"hinnat",	u"hinnalta",	u"hintana"),#	price
	(u"linnun",	u"lintu",	u"linnut",	u"linnulta",	u"lintuna"),#	bird
	(u"opinnon",	u"opinto",	u"opinnot",	u"opinnolta",	u"opintona"),#	study
	(u"rannan",	u"ranta",	u"rannat",	u"rannalta",	u"rantana"),#	shore
	(u"luonnon",	u"luonto",	u"luonnot",	u"luonnolta",	u"luontona"),#	nature
	(u"punnan",	u"punta",	u"punnat",	u"punnalta",	u"puntana"),#	pound
	(u"tunnin",	u"tunti",	u"tunnit",	u"tunnilta",	u"tuntina"),#	hour
	(u"kunnon",	u"kunto",	u"kunnot",	u"kunnolta",	u"kuntona"),#	condition
	(u"kannun",	u"kannu",	u"kannut",	u"kannulta",	u"kannuna"),#	can
	(u"linnan",	u"linna",	u"linnat",	u"linnalta",	u"linnana"),#	castle
	(u"tumman",	u"tumma",	u"tummat",	u"tummalta",	u"tummana"),#	dark
	(u"auriŋŋon",	u"auriŋko",	u"auriŋŋot",	u"auriŋŋolta",	u"auriŋkona"),#	sun
	(u"reŋŋin",	u"reŋki",	u"reŋŋit",	u"reŋŋiltæ",	u"reŋkinæ"),#	farm hand
	(u"vaŋŋin",	u"vaŋki",	u"vaŋŋit",	u"vaŋŋilta",	u"vaŋkina"),#	prisoner
	(u"kellon",	u"kello",	u"kellot",	u"kellolta",	u"kellona"),#	watch
	(u"kellan",	u"kelta",	u"kellat",	u"kellalta",	u"keltana"),#	yellow
	(u"sillan",	u"silta",	u"sillat",	u"sillalta",	u"siltana"),#	bridge
	(u"kullan",	u"kulta",	u"kullat ",	u"kullalta ",	u"kultana "),#	gold
	(u"virran",	u"virta",	u"virrat",	u"virralta",	u"virtana"),#	stream
	(u"parran",	u"parta",	u"parrat",	u"parralta",	u"partana")],#	beard
    solutions = [u'''
 + stem + n
 + stem + 
 + stem + t
 + stem + lta
 + stem + na
a > æ / æ C* _
k > 0 / []_V[-lateral] 
''']))

interactingProblems.append(Problem(
    '''7: Korean
Provide rules which will account for the alternations in the stem final consonant in the following examples. State what underlying representation you are assuming for each noun.
    ''',
    #	‘rice’	‘forest’	‘chestnut’	‘field’	‘sickle’	‘day’	‘face’	‘half’	
transposeInflections([
    (u"pamman",	u"summan",	u"pamman", u"pamman",	u"namman",	u"namman", u"namman",	u"pamman"),#	only N
    (u"pammaŋk^hɨm",	u"summaŋk^hɨm",	u"pammaŋk^hɨm", u"pammaŋk^hɨm",	u"nammaŋk^hɨm",	u"nammaŋk^hɨm", u"nammaŋk^hɨm",	u"pammaŋk^hɨm"),#	as much as N
    (u"pamnarɨm",	u"sumnarɨm",	u"pamnarɨm", u"pannarɨm",	u"nannarɨm",	u"nannarɨm", u"nannarɨm",	u"pannarɨm"),#	depending on N
    (u"pap",	u"sup",	u"pam", u"pat",	u"nat",	u"nat", u"nat",	u"pan"),#	N
    (u"papt’ero",	u"supt’ero",	u"pamtero", u"patt’ero",	u"natt’ero",	u"natt’ero", u"natt’ero",	u"pantero"),#	like N
    (u"papk’wa",	u"supk’wa",	u"pamkwa", u"pakk’wa",	u"nakk’wa",	u"nakk’wa", u"nakk’wa",	u"paŋkwa"),#	with N
    (u"papp’ota",	u"supp’ota",	u"pampota", u"papp’ota",	u"napp’ota",	u"napp’ota", u"napp’ota",	u"pampota"),#	more than N
    (u"papk’ači",	u"supk’ači",	u"pamk’ači", u"pakk’ači",	u"nakk’ači",	u"nakk’ači", u"nakk’ači",	u"paŋk’ači"),#	until N
    (u"papi",	u"sup^hi",	u"pami", u"pač^hi",	u"nasi",	u"nači", u"nač^hi",	u"pani"),#	N (nominative)
    (u"papɨn",	u"sup^hɨn",	u"pamɨn", u"pat^hɨn",	u"nasɨn",	u"načɨn", u"nač^hɨn",	u"panɨn"),#	N (topic)
    (u"pape",	u"sup^he",	u"pame", u"pat^he",	u"nase",	u"nače", u"nač^he",	u"pane"),#	to N
    (u"papita",	u"sup^hita",	u"pamita", u"pač^hita",	u"nasita",	u"načita", u"nač^hita",	u"panita"),#	it is N
    (u"papɨro",	u"sup^hɨro",	u"pamɨro", u"pat^hɨro",	u"nasɨro",	u"načɨro", u"nač^hɨro",	u"panɨro")]),#	using N
    solutions = [u'''
 + stem + man
 + stem + maŋk^hɨm
 + stem + narɨm
 + stem + 
 + stem + tero
 + stem + kwa
 + stem + pota
 + stem + kači
 + stem + i
 + stem + ɨn
 + stem + e
 + stem + ita
 + stem + ɨro
    C > [-aspirated]/_{#,C}
    p > m/_[+nasal]''']))



sevenProblems = []
sevenProblems.append(Problem(
'''
1: Serbo-Croatian
	These data from Serbo-Croatian have been simplified in two ways, to make the problem more manageable. Vowel length is omitted, and the only accent that is included is the predictable accent. Invariant lexical acent is not marked, and your analysis should explain how accent is assigned in the predictable-accent class, where accent is marked. You cannot write rules which predict accent for those words in the unpredictable accent class, and you cannot (and should not try to) write a rule which somehow predicts whether a word receives a predictable accent. Ignore the accent of words with no accent mark (other parts of the phonology of such words must be accounted for). Past tense verbs all have the same general past tense suffix, and that the difference between masculine, feminine and neuter past tense involves the same suffixes as are used to mark gender in adjectives.
''',
#	Adjectives
#	Masc.	Fem.	Neut.	Pl.
	[
            (u"mlád",	u"mladá",	u"mladó",	u"mladí",None,None,None,None),#	young
            (u"túp",	u"tupá",	u"tupó",	u"tupí",None,None,None,None),#	blunt
            (u"blág",	u"blagá",	u"blagó",	u"blagí",None,None,None,None),#	mild
            (u"grúb",	u"grubá",	u"grubó",	u"grubí",None,None,None,None),#	coarse
            (u"križan",	u"križana",	u"križano",	u"križani",None,None,None,None),#	cross
            (u"sunčan", 	u"sunčana", 	u"sunčano", 	u"sunčani",None,None,None,None),#	sunny
            (u"svečan", 	u"svečana", 	u"svečano", 	u"svečani",None,None,None,None),#	formal
            (u"béo",	u"belá",	u"beló",	u"belí",None,None,None,None),#	white
            (u"veseo",	u"vesela",	u"veselo",	u"veseli",None,None,None,None),#	gay
            (u"debéo",	u"debelá",	u"debeló",	u"debelí",None,None,None,None),#	fat
            (u"mío",	u"milá",	u"miló",	u"milí",None,None,None,None),#	dear
            (u"zelén",	u"zelená",	u"zelenó",	u"zelení",None,None,None,None),#	green
            (u"kradén",	u"kradená", 	u"kradenó", 	u"kradení",None,None,None,None),#	stolen
            (u"dalék",	u"daleká", 	u"dalekó", 	u"dalekí",None,None,None,None),#	far
            (u"visók",	u"visoká", 	u"visokó", 	u"visokí",None,None,None,None),#	high
            (u"dubók",	u"duboká",	u"dubokó",	u"dubokí",None,None,None,None),#	deep
            (u"bogat",	u"bogata",	u"bogato",	u"bogati",None,None,None,None),#	rich
            (u"rapav",	u"rapava",	u"rapavo",	u"rapavi",None,None,None,None),#	rough
            (u"yásan",	u"yasná",	u"yasnó",	u"yasní",None,None,None,None),#	clear
            (u"vážan",	u"važná",	u"važnó",	u"važní",None,None,None,None),#	important
            (u"sítan",	u"sitná",	u"sitnó",	u"sitní",None,None,None,None),#	tiny
            (u"ledan",	u"ledna",	u"ledno",	u"ledni",None,None,None,None),#	frozen
            (u"tának",	u"tanká",	u"tankó",	u"tankí",None,None,None,None),#	slim
            (u"krátak",	u"kratká",	u"kratkó",	u"kratkí",None,None,None,None),#	short
            (u"blízak",	u"bliská",	u"bliskó",	u"bliskí",None,None,None,None),#	close
            (u"úzak",	u"uská",	u"uskó",	u"uskí",None,None,None,None),#	narrow
            (u"dóbar",	u"dobrá",	u"dobró",	u"dobrí",None,None,None,None),#	kind
            (u"óštar",	u"oštrá",	u"oštró",	u"oštrí",None,None,None,None),#	sharp
            (u"bodar",	u"bodra",	u"bodro",	u"bodri",None,None,None,None),#	alert
            (u"ustao",	u"ustala",	u"ustalo",	u"ustali",None,None,None,None),#	tired
            (u"múkao",	u"muklá",	u"mukló",	u"muklí",None,None,None,None),#	hoarse
            (u"óbao",	u"oblá",	u"obló",	u"oblí",None,None,None,None),#	plump
            (u"pódao",	u"podlá",	u"podló",	u"podlí",None,None,None,None),#	base

	# Verbs
	# 1sg pres	masc. past	fem. past	neut. past	
	    (None,None,None,None,u"tepém",	u"tépao",	u"teplá",	u"tepló"),#	wander
	    (None,None,None,None,u"skubém",	u"skúbao",	u"skublá",	u"skubló"),#	tear
	    (None,None,None,None,u"tresém",	u"trésao",	u"treslá",	u"tresló"),#shake
	    (None,None,None,None,u"vezém",	u"vézao",	u"vezlá",	u"vezló")],#	lead
    solutions = [u'''
 + stem + 
 + stem + a
 + stem + o
 + stem + i
 + stem + em
 + stem + l
 + stem + la
 + stem + lo
V > [+highTone]/[+highTone]C*_
V > [-highTone]/_C*[+highTone]
0 > a/C_C#
l > o/_#
[-sonorant] > [-voice]/_[-voice]
''']))


sevenProblems.append(Problem('''2: Standard Ukrainian
	Standard Ukrainian has palatalized and non-palatalized consonants, but only non-palatalized consonants before e. Consonants are generally palatalized before i, with some apparent exceptions such as bily ‘ache’, which need not be seen as exceptions, given the right analysis. Give ordered rules to account for the alternations of the following nouns. The alternation between o and e is limited to suffixes. Also for masculine nouns referring to persons, ov/ev is inserted between the root and the case suffix in the locative singular (see ‘son-in-law’, ‘grandfather’). The data are initially ambiguous as to whether or not the alternations between o and i and between e and i are to be implemented by the same rule. Consider both possibilities; give an argument for selecting one of these solutions. 
''',
#	Masculine nouns
#	Nom. sg.	Dat. pl. 	 Dat. sg.	Loc. sg.	Gloss
[
	(u"zub",	u"zubam",	u"zubov^yi",	u"zub^yi",None,None,None,None,None,None),#	tooth
	(u"sv^yit",	u"sv^yitam",	u"sv^yitov^yi",	u"sv^yit^yi",None,None,None,None,None,None),#	light
	(u"z^yat^y",	u"z^yat^yam",	u"z^yatev^yi",	None,u"z^yatev^yi",None,None,None,None,None),#	son-in-law
	(u"koš^yil^y",	u"košel^yam",	u"košelev^yi",	u"košel^yi",None,None,None,None,None,None),#	basket
	(u"zlod^yiy",	u"zlod^yiyam",	u"zlod^yiyev^yi",	None,u"zlod^yiyev^yi",None,None,None,None,None),# 	thief
	(u"m^yis^yat^s^y",	u"m^yis^yat^s^yam",	u"m^yis^yat^sev^yi",	u"m^yis^yat^s^yi",None,None,None,None,None,None),#	month
	(u"korovay",	u"korovayam",	u"korovayev^yi",	u"korovayi",None,None,None,None,None,None),#	round loaf
	(u"kam^yin^y",	u"kamen^yam",	u"kamenev^yi",	u"kamen^yi",None,None,None,None,None,None),#	stone
	(u"m^yid^y",	u"m^yid^yam",	u"m^yidev^yi",	u"m^yid^yi",None,None,None,None,None,None),#	copper
	(u"xl^yiw",	u"xl^yivam",	u"xl^yivov^yi",	u"xl^yiv^yi",None,None,None,None,None,None),#	stable
	(u"holub",	u"holubam",	u"holubov^yi",	u"holub^yi",None,None,None,None,None,None),#	dove
	(u"s^yin",	u"s^yinam",	u"s^yinov^yi",	u"s^yin^yi",None,None,None,None,None,None),#	son
	(u"leb^yid^y",	u"lebed^yam",	u"lebedev^yi",	u"lebed^yi",None,None,None,None,None,None),#	swan
	(u"sus^yid", 	u"sus^yidam", 	u"sus^yidov^yi", 	None,u"sus^yidov^yi",None,None,None,None,None),#	neighbor
	(u"čolov^yik", 	u"čolov^yikam", 	u"čolov^yikov^yi", 	None,u"čolov^yikov^yi",None,None,None,None,None),#	man
	(u"l^yid",	u"ledam",	u"ledov^yi",	u"led^yi",None,None,None,None,None,None),#	ice
	(u"bil^y",	u"bol^yam",	u"bolev^yi",	u"bol^yi",None,None,None,None,None,None),#	ache
	(u"riw",	u"rovam",	u"rovov^yi",	u"rov^yi",None,None,None,None,None,None),#	ditch
	(u"stiw",	u"stolam",	u"stolov^yi",	u"stol^yi",None,None,None,None,None,None),#	table
	(u"d^yid",	u"d^yidam",	u"d^yidov^yi",	None,u"d^yidov^yi",None,None,None,None,None),#	grandfather
	(u"l^yit",	u"l^yotam",	u"l^yotov^yi",	u"l^yot^yi",None,None,None,None,None,None),#	flight
	(u"mist",	u"mostam",	u"mostov^yi",	u"most^yi",None,None,None,None,None,None),#	bridge
	(u"večir",	u"večoram",	u"večorov^yi",	u"večor^yi",None,None,None,None,None,None),#	evening
	
	# Neuter nouns
	# Nom. sg.	Gen. sg.	Dat. sg.	Loc. sg.	Gen. pl.	Gloss
    
    (None,None,None,None,None,u"t^yilo",	u"t^yila",	u"t^yilu",	u"t^yil^yi",	u"t^yiw"),#	body
    (None,None,None,None,None,u"koleso",	u"kolesa",	u"kolesu",	u"koles^yi",	u"kol^yis"),#	wheel
    (None,None,None,None,None,u"ozero",	u"ozera",	u"ozeru",	u"ozer^yi",	u"oz^yir"), # lake
    (None,None,None,None,None,u"selo",	u"sela",	u"selu",	u"sel^yi",	u"s^yiw"), # village
    (None,None,None,None,None,u"pole",	u"pol^ya",	u"pol^yu",	u"pol^yi",	u"pil^y"), # field
    (None,None,None,None,None,u"slovo",	u"slova",	u"slovu",	u"slov^yi",	u"sliw"), # word
    (None,None,None,None,None,u"more",	u"mor^ya",	u"mor^yu",	u"mor^yi",	u"mir^y"), # sea
],
                             solutions = 
[u''' + stem + 
 + stem + am
 + stem + ov^yi
 + stem + i
 + stem + ov^yi
 + stem + o
 + stem + a
 + stem + u
 + stem + i
 + stem + 
C > [+palletized] / _ i ;; i is the only thing in the data which is [+high -back]
o > e / [+palletized] + _ ;; i is the only thing that is [+vowel +high -back]. "vowel fronting"
[+vowel -low -high] > i / _ C* C # ;; neutralize {e,o} if they are the last vowel
[-glide -vowel] > [-palletized] / _ e ;; depalletized anything except for y
l > w/_# ;; l = [liquid,lateral,voice,alveolar,coronal,sonorant]
v > w/_# ;; v = [labiodental,fricative,voice]
''']))

sevenProblems.append(Problem('''3: Somali
	In the following Somali data, [ḍ] is a voiced retroflex stop and [ṛ] is a voiced retroflex spirant. Account for all phonological alternations in these data. In your discussion of these forms, be sure to make it clear what you assume the underlying representations of relevant morphemes are. Your discussion should also make it clear what motivates your underlying representations and rules. For instance if you could analyse some alternation by assuming underlying X and rule Y, say why (or whether) that choice is preferable to the alternative of assuming underlying P and rule Q.
Kevin analysis:
Morphology:
stem
stem + /ta/
stem + /o/
(these are wrong...)
{g,b,d} > {ɣ,β,ð} / _o#
ḍ > ṛ / _o#
''',
[
#	Singular	Sing. Definite	Plural	Gloss
    # illustrates morphology
	(u"daar",	u"daarta",	u"daaro",None,None,None),#	house
	(u"gees",	u"geesta",	u"geeso",None,None,None),#	side
	(u"laf",	u"lafta",	u"lafo",None,None,None),#	bone
    # illustrate stop/fricative alternations
	(u"lug",	u"lugta",  	u"luɣo",None,None,None),#	leg
	(u"naag",	u"naagta",	u"naaɣo",None,None,None),#	woman
	(u"tib",	u"tibta",    	u"tiβo",None,None,None),#	pestle
	(u"sab",	u"sabta",    	u"saβo",None,None,None),#	outcast
    # illustrates /t/ deletion
	(u"bad",	u"bada",	u"baðo",None,None,None),#	sea
	(u"šid",	u"šida",	u"šiðo",None,None,None),#	person
    # 
	(u"feeḍ",	u"feeḍa",  	u"feeṛo",None,None,None),#	rib
	(u"ʕiir",	u"ʕiirta",	u"ʕiiro",None,None,None),#	buttermilk
	(u"ʔul",	u"ʔuša",	u"ʔulo",None,None,None),#	stick
	(u"bil",	u"biša",	u"bilo",None,None,None),#	month
	(u"meel",	u"meeša",	u"meelo",None,None,None),#	place
	(u"kaliil",	u"kaliiša",	u"kaliilo",None,None,None),#	summer
	(u"nayl",	u"nayša",	u"naylo",None,None,None),#	female lamb
	(u"sun",	u"sunta",	u"sumo",None,None,None),#	poison
	(u"laan",	u"laanta",	u"laamo",None,None,None),#	branch
	(u"sin",	u"sinta",	u"simo",None,None,None),#	hip
	(u"dan",	u"danta",	u"dano",None,None,None),#	affair
	(u"daan",	u"daanta",	u"daano",None,None,None),#	river bank
	(u"saan",	u"saanta",	u"saano",None,None,None),#	hide
	(u"nirig",	u"nirigta",	u"nirgo",None,None,None),#	baby female camel
	(u"gaβaḍ",	u"gaβaḍa",	u"gabḍo",None,None,None),#	girl
	(u"hoɣol",	u"hoɣoša",	u"hoglo",None,None,None),#	downpour
	(u"baɣal",	u"baɣaša",	u"baglo",None,None,None),#	mule
	(u"waħar",	u"waħarta",	u"waħaro",None,None,None),#	female kid
	(u"irbad",	u"irbada",	u"irbaðo",None,None,None),#	needle
	(u"kefed",	u"kefeda",	u"kefeðo",None,None,None),#	pan
	(u"šilin",	u"šilinta",	u"šilino",None,None,None),#	female dwarf
	(u"bohol",	u"bohoša",	u"boholo",None,None,None),#	hole
    # todo: figure out what /j/ is supposed to be
	#(u"jirid",	u"jirida",	u"jirdo"),#	trunk
	(u"ʔaayad",	u"ʔaayada",	u"ʔaayaðo",None,None,None),#	miracle
	(u"gaʕan",	u"gaʕanta",	u"gaʕmo",None,None,None),#	hand
	(u"ʔinan",	u"ʔinanta",	u"ʔinano",None,None,None),#	daughter

	# 3sg msc. pst	3sg fem. past	1pl past	Gloss
	(None,None,None, u"suɣay",	u"sugtay",	u"sugnay"),#	wait
	(None,None,None, u"kaβay",	u"kabtay",	u"kabnay"),#	fix
	(None,None,None, u"siðay",	u"siday",	u"sidnay"),#	carry
	(None,None,None, u"dilay",	u"dišay",	u"dillay"),#	kill
	(None,None,None, u"ganay",	u"gantay",	u"gannay"),#	aim
	(None,None,None, u"tumay",	u"tuntay",	u"tunnay"),#	hammer
	(None,None,None, u"argay",	u"aragtay",	u"aragnay"),#	see
	(None,None,None, u"gudbay",	u"guðubtay",	u"guðubnay"),#	cross a river
	(None,None,None, u"qoslay",	u"qosošay",	u"qosollay"),#	laugh
	(None,None,None, u"hadlay",	u"haðašay",	u"haðallay"),#	talk
], solutions = [u'''
 + stem + 
 + stem + ta
 + stem + o
 + stem + ay
 + stem + tay
 + stem + nay
0 > -2/V[-vowel -glide]_C{#,C}
[-sonorant +voice] > [+continuant] / V_V
m > n/_{#,C}
t > 0/[+coronal -sonorant -continuant]_a
n > l/l_
t > š/l_
l > 0/_š
''']))

sevenProblems.append(Problem('''4: Latin
	Provide a complete account of the following phonological alternations in Latin, including underlying forms for nouns stems.
''',
[
#	Nominative		Genitive  		Gloss
    # illustrate the morphology
	(u"arks",			u"arkis",None),#			fortress
	(u"duks",			u"dukis",None),#			leader
	(u"daps",			u"dapis",None),#			feast
    # illustrate devoicing
	(u"re:ks",			u"re:gis",None),#			king
	(u"falanks",		u"falangis",None),#		phalanx
	(u"filiks",			u"filikis",None),#			fern
    # illustrate t/d deletion
	(u"lapis",			u"lapidis",None),#   		stone
	(u"li:s",			u"li:tis",None),#			strife
	(u"fraws",			u"frawdis",None),#   		deceit
	(u"noks",			u"noktis",None),#    		night
	(u"frons",			u"frontis",None),#   		brow
	(u"frons",			u"frondis",None),#   		leaf
	(u"inku:s",			u"inku:dis",None),#  		anvil
	(u"sors",			u"sortis",None),#			lot
    # illustrate s deletion: occurs after +son -vowel
	(u"fu:r",			u"fu:ris",None),#			thief
	(u"murmur",    		u"murmuris",None),#  		murmur
	(u"augur",     		u"auguris",None),#   		augur
	(u"arbor",			u"arboris",None),#   		tree
	(u"pugil",			u"pugilis",None),#   		boxer
	(u"sal",			u"salis",None),#			salt
    # illustrate vowel harmony
	(u"adeps",			u"adipis",None),#			fat
	(u"apeks",			u"apikis",None),#			top
	(u"pri:nkeps", 		u"pri:nkipis",None),#		chief
	(u"ekwes",			u"ekwitis",None),#   		horseman
	(u"miles",			u"militis",None),#   		soldier
	(u"no:men",    		u"no:minis",None),#  		name
	(u"karmen",    		u"karminis",None),# 		song
	(u"lu:men",    		u"lu:minis",None),#  		light
    # illustrate /e/ insertion & blocking of the vowel harmony
	(u"wenter",    		u"wentris",None),#   		belly
	(u"pater",			u"patris",None),#			father
	(u"kada:wer",  		u"kada:weris",None),#		corpse
	(u"tu:ber",			u"tu:beris",None),#  		swelling
	(u"piper",			u"piperis",None),#   		pepper
	(u"karker",    		u"karkeris",None),#  		prison
	
# 	The following 6 nouns and adjectives select a different genitive suffix, -i: as opposed to is. You cannot predict on phonological grounds what nouns take this suffix, but otherwise these words follow the rules motivated in the language.
	
 	(u"die:s",	None,u"die:i:"),#	day
 	(u"li:ber",	None,u"li:beri:"),#	free
 	(u"miser",	None,u"miseri:"),#   	wretched
    # illustrates another condition for /e/ insertion
 	(u"ager",	None,u"agri:"),#	field
 	(u"sinister",  	None,u"sinistri:"),# 	left
 	(u"liber",	None,u"libri:"),#	book

# What other phonological rule or rules are needed to account for the following data?
    # C_i > 0 / _ C_i #
	(u"as",			u"assis",None),#			whole
	(u"os",			u"ossis",None),#			bone
	(u"far",			u"farris",None),#			spell
	(u"mel",			u"mellis",None),#			honey
    # # /r/ creation: s > r/V_V
        (u"o:s",			u"o:ris",None),#			mouth
        (u"flo:s",			u"flo:ris",None),#			flower
        (u"mu:s",			u"mu:ris",None),#		mouse
        (u"cru:s",			u"cru:ris",None),#		leg
        (u"kinis",			u"kineris",None),#		ash
        (u"pulvis",		u"pulveris",None),#		dust
    ],
                             solutions = [u'''
 + stem + s
 + stem + is
 + stem + i:
                             [-sonorant] > [-voice] / _ [-voice]
                             s > 0/[+coronal +sonorant] _
                             [+coronal -sonorant] > 0 / _s
                             e > i/_CV ;;[+vowel -back -long] > [+high]/_CV ;; e > i
                             0 > e/ C_[+coronal +sonorant]#
                             s > r/V_V
                             [+vowel -back] > [-high]/_r
                             1 > 0/_C# ;; this isn't working
                             
''']))
	
sevenProblems.append(Problem('''5: Turkish
	Provide a phonological analysis of the following data from Turkish.
My analysis:
Morphology: 
stem
stem + /s
''',[
    
#	nom	poss	dat	abl	nom. pl
	(u"oda",	u"odasɨ",	u"odaya",	u"odadan",	u"odalar"),#	room
	(u"dere",	u"deresi",	u"dereye",	u"dereden",	u"dereler"),#	river
	(u"ütü",	u"ütüsü",	u"ütüye",	u"ütüden",	u"ütüler"),#	iron
	(u"balo",	u"balosu",	u"baloya",	u"balodan",	u"balolar"),#	ball
	(u"arɨ",	u"arɨsɨ", 	u"arɨya",	u"arɨdan",	u"arɨlar"),#	bee
	(u"la:",	u"la:sɨ",	u"la:ya",	u"la:dan",	u"la:lar"),#	la (note)
	(u"bina:",	u"bina:sɨ",	u"bina:ya",	u"bina:dan",	u"bina:lar"),#	building
	(u"imla:",	u"imla:sɨ",	u"imla:ya",	u"imla:dan",	u"imla:lar"),#	spelling
	(u"be:",	u"be:si",	u"be:ye",	u"be:den",	u"be:ler"),#	B (letter)
	(u"kep",	u"kepi",	u"kepe",	u"kepten",	u"kepler"),#	cap
	(u"at",	u"atɨ",	u"ata",	u"attan",	u"atlar"),#	horse
	(u"ek",	u"eki",	u"eke",	u"ekten",	u"ekler"),#	affix
	(u"ok",	u"oku",	u"oka",	u"oktan",	u"oklar"),#	arrow
	(u"güč",	u"güǰü",	u"güǰe",	u"güčten",	u"güčler"),#	power
	(u"ahmet",	u"ahmedi",	u"ahmede",	u"ahmetten",	u"ahmetler"),#	Ahmed
	(u"kurt",	u"kurdu",	u"kurda",	u"kurttan",	u"kurtlar"),#	worm
	(u"türk",	u"türkü",	u"türke",	u"türkten",	u"türkler"),#	Turk
	(u"genč",	u"genči",	u"genče",	u"genčten",	u"genčler"),#	young
	(u"halk",	u"halkɨ",	u"halka",	u"halktan",	u"halklar"),#	folk
	(u"üst",	u"üstü",	u"üste",	u"üstten",	u"üstler"),#	upper plane
	(u"sarp",	u"sarpɨ",	u"sarpa",	u"sarptan",	u"sarplar"),#	steep
	(u"harp",	u"harbɨ",	u"harba",	u"harptan",	u"harplar"),#	war
	(u"alt",	u"altɨ",	u"alta",	u"alttan",	u"altlar"),#	bottom
	(u"renk",	u"rengi",	u"renge",	u"renkten",	u"renkler"),#	color
	(u"his",	u"hissi",	u"hisse",	u"histen",	u"hisler"),#	feeling
	(u"hür",	u"hürrü",	u"hürre",	u"hürden",	u"hürler"),#	free
	(u"mahal",	u"mahallɨ",	u"mahalla",	u"mahaldan",	u"mahallar"),#	place
	(u"hak",	u"hakkɨ",	u"hakka",	u"haktan",	u"haklar"),#	right
	(u"zam",	u"zammɨ",	u"zamma",	u"zamdan",	u"zamlar"),#	inflation
	(u"af",	u"affɨ",	u"affa",	u"aftan",	u"aflar"),#	excuse
	(u"arap",	u"arabɨ",	u"araba",	u"araptan",	u"araplar"),#	Arab
	(u"koyun",	u"koyunu",	u"koyuna",	u"koyundan",	u"koyunlar"),#	sheep
	(u"pilot",	u"pilotu",	u"pilota",	u"pilottan",	u"pilotlar"),#	pilot
	(u"kitap",	u"kitabɨ",	u"kitaba",	u"kitaptan",	u"kitaplar"),#	book
	(u"domuz",	u"domuzu",	u"domuza",	u"domuzdan",	u"domuzlar"),#	pig
	(u"davul",	u"davulu",	u"davula",	u"davuldan",	u"davullar"),#	drum
	(u"bayɨr",	u"bayɨrɨ",	u"bayɨra",	u"bayɨrdan",	u"bayɨrlar"),#	slope
	(u"somun",	u"somunu",	u"somuna",	u"somundan",	u"somunlar"),#	loaf
	(u"fikir",	u"fikri",	u"fikre",	u"fikirden",	u"fikirler"),#	idea
	(u"isim",	u"ismi",	u"isme",	u"isimden",	u"isimler"),#	name
	(u"boyun",	u"boynu",	u"boyna",	u"boyundan",	u"boyunlar"),#	neck
	(u"čevir",	u"čevri",	u"čevre",	u"čevirden",	u"čevirler"),#	injustice
	(u"devir",	u"devri",	u"devre",	u"devirden",	u"devirler"),#	transfer
	(u"koyun",	u"koynu",	u"koyna",	u"koyundan",	u"koyunlar"),#	bosom
	(u"karɨn",	u"karnɨ",	u"karna",	u"karɨndan",	u"karɨnlar"),#	thorax
	(u"burun",	u"burnu",	u"burna",	u"burundan",	u"burunlar"),#	nose
	(u"akɨl",	u"aklɨ",	u"akla",	u"akɨldan",	u"akɨllar"),#	intelligence
	(u"šehir",	u"šehri",	u"šehre",	u"šehirden",	u"šehirler"),#	city
	(u"namaz",	u"namazɨ",	u"namaza",	u"namazdan",	u"namazlar"),#	worship
	(u"zaman",	u"zama:nɨ",	u"zama:na",	u"zamandan",	u"zamanlar"),#	time
	(u"harap",	u"hara:bɨ",	u"hara:ba",	u"haraptan",	u"haraplar"),#	ruined
	(u"i:kaz",	u"i:ka:zɨ",	u"i:ka:za",	u"i:kazdan",	u"i:kazlar"),#	warning
	(u"hayat",	u"haya:tɨ",	u"haya:ta",	u"hayattan",	u"hayatlar"),#	life
	(u"ispat",	u"ispa:tɨ",	u"ispa:ta",	u"ispattan",	u"ispatlar"),#	proof
	(u"inek",	u"inei",	u"inee",	u"inekten",	u"inekler"),#	cow
	(u"mantɨk",	u"mantɨɨ",	u"mantɨa",	u"mantɨktan",	u"mantɨklar"),#	logic
	(u"ayak",	u"ayaɨ",	u"ayaa",	u"ayaktan",	u"ayaklar"),#	foot
	(u"čabuk",	u"čabuu",	u"čabua",	u"čabuktan",	u"čabuklar"),#	quick
	(u"dakik",	u"dakii",	u"dakie",	u"dakikten",	u"dakikler"),#	punctual
	(u"merak",	u"mera:kɨ",	u"mera:ka",	u"meraktan",	u"meraklar"),#	curiosity
	(u"tebrik",	u"tebri:ki",	u"tebri:ke",	u"tebrikten",	u"tebrikler"),#	greetings
	(u"hukuk",	u"huku:ku",	u"huku:ka",	u"hukuktan",	u"hukuklar"),#	law
]))

sevenProblems.append(Problem('''6: Kera
	Propose rules to account for the following alternations. It will prove useful to think about Kera vowels in terms of high versus non-high vowels. Also, in this language it would be convenient to assume that [h] and [ʔ] are specified as [+low]. Pay attention to both verbs like bɨlan ‘want me’, balnan ‘wanted me’ and bal-l-a ‘you must want!’, i.e. there are present, past and imperative forms involved, certain tenses being marked by suffixes. Finally, pay attention to what might look like a coincidence in the distribution of vowels in the underlying forms of verb roots: there are no coincidences.
''',
	[(u'haman',#  	‘eat me’	
	  u'hamam',#  	‘eat you m.’	
	  u'hɨmi',#	‘eat you f.’	
	  u'hɨmu',#	‘eat him’	
	  u'hama',#	‘eat her’	
	  u'hamaŋ'),#  	‘eat you pl.’	

         (u"se:nen",#	‘my brother’
          u"se:nem",# 	‘your masc. brother’
          u"si:ni",#	‘your fem. brother’
          u"si:nu",#	‘his brother’
          u"se:na",#	‘her brother’
          u"se:neŋ"),#	‘your pl. brother’
         
	(u'kolon',#,	‘change me’	
	u'kolom',#	‘change you masc.’	
	 u'kuli',#	‘change you fem.’	
	 u'kulu',#	‘change him’	
	 u'kola',#	‘change her’	
	 u'koloŋ'),#	‘change you pl.’	

         (u"gi:din",#	‘my belly’
          u"gi:dim",#	‘your masc. belly’
          u"gi:di",#	‘your fem. belly’
          u"gi:du",#	‘his belly’
          u"gi:dɨ",#	‘her belly’
          u"gi:diŋ"),#	‘your pl. belly’
         
	(u'cɨ:rɨn',#	‘my head’	
	 u'cɨ:rɨm',#	‘your masc. head’	
	 u'ci:ri',#	‘your fem. head’	
	 u'cu:ru',#	‘his head’	
	 u'cɨ:rɨ',#	‘her head’	
	 u'cɨ:rɨŋ'),#	‘your pl. head’	

         (u"gunun",#	‘wake me’
          u"gunum",# 	‘wake you masc.’
          u"guni",#	‘wake you fem.’
          u"gunu",#	‘wake him’
          u"gunɨ",#	‘wake her’
          u"gunuŋ"),#	‘wake you pl.’
         
	(u'bɨlan',#	‘want me’	
	 u'bɨlam',#	‘want you masc.’	
	 u'bɨli',#	‘want you fem.’	
	 u'bɨlu',#	‘want him’	
	 u'bɨla',#	‘want her’	
	 u'bɨlaŋ'),#	‘want you pl.’	

         (u'ŋɨfan',#	‘meet me’
          u'ŋɨfam',#	‘meet you masc.’
          u'ŋɨfi',#	‘meet you fem.’
          u'ŋɨfu',#	‘meet him’
          u'ŋɨfa',#	‘meet her’
          u'ŋɨfaŋ'),#	‘meet you pl.’
         
	(u'ʔasan',#	‘know me’	
	 u'ʔasam',#	‘know you masc.’	
	 u'ʔɨsi',#	‘know you fem.’	
	 u'ʔɨsu',#	‘know him’	
	 u'ʔasa',#	‘know her’	
	 u'ʔasaŋ'),#	‘know you pl.’	

         (u'ʔapan',#	‘find me’
          u'ʔapam',#	‘find you masc.’
          u'ʔɨpi',#	‘find you fem.’
          u'ʔɨpu',#	‘find him’
          u'ʔapa',#	‘find her’
          u'ʔapaŋ'),#	‘find you pl.’
         
	(u'haran',#	‘give me back’
	 u'haram',#	‘give you masc. back’
	 u'hɨri',#	‘give you fem. back’
	 u'hɨru',#	‘give him back’
	 u'hara',#	‘give her back’
	 u'haraŋ'),#	‘give you pl. back’
	 
	(u'balnan',#  	‘wanted me’	
	 u'balnam',# 	wanted you masc.’	
	 u'bɨlni',#	‘wanted you fem.’	
	 u'bɨlnu',#	‘wanted him’	
	 u'balna',#	‘wanted her’	
	 u'balnaŋ'),#  	‘wanted you pl.’	

         (u'ŋafnan ',#	‘met me’
          u'ŋafnam',#	‘met you masc.’
          u'ŋɨfni',#	‘met you fem.’
          u'ŋɨfnu',#	‘met him’
          u'ŋafna',#	‘met her’
          u'ŋafnaŋ')# 	‘met you pl.’
         
#todo
         
	 # bal-l-a	‘you must want!’	ŋaf-l-a	‘you must meet!’
	 
	# ba	‘not’	pa	‘again’	bɨ-pa	‘no more’
        ],
                             solutions = [u'''
 + stem + n
 + stem + m
 + stem + i
 + stem + u
 + stem + a
 + stem + ŋ
0 > -2/VC_C#
V > [-long]/ _ C #
ɨ > i/_C*i#
ɨ > u/_C*u#
V > [-low +high]/_C*[+high]
V > [-low +high]/[+high]C*_
a > ɨ/[-low]_Ca
''']))

sevenProblems.append(Problem('''7: Keley-i
	Account for the alternations in the following verbs. The different forms relate to whether the action is in the past or future, and which element in the sentence is emphasised (subject, object, instrument). Roots underlyingly have the shape CVC(C)VC, and certain forms such as the subject focus future require changes in the stem that result in a CVCCVC shape. This may be accomplished by reduplicating the initial CV- for stems whose first vowel is [e] (ʔum-bebhat – behat) or doubling the middle consonant (ʔum-buŋŋet – buŋet). The contrastive identification imperfective form conditions lengthening of the consonant in the middle of the stem, when the first vowel is not [e] (memayyuʔ – bayuʔ). These changes are part of the morphology, so do not attempt to write phonological rules to double consonants or reduplicate syllables. Be sure to explicitly state the underlying form of each root and affix. Understanding the status of [s] and [h] in this language is important in solving this problem. It is also important to consider exactly what underlying nasal consonant is present in these various prefixes and infixes – there is evidence in the data which shows that the underlying nature of the nasal explains certain observed differences in phonological behavior.
''',
#	subject focus	direct object	instrumental focus
#	future	focus past	past
[
	(u"ʔumduntuk",	u"dinuntuk",	u"ʔinduntuk", u"ʔinduntuk",	u"menuntuk",	u"nenuntuk"),#	punch
	(u"ʔumbayyuʔ",	u"binayuʔ",	u"ʔimbayuʔ", u"ʔimbayuʔ",	u"memayyuʔ",	u"nemayuʔ"),#	pound rice
	(u"ʔumdillag",	u"dinilag",	u"ʔindilag", u"ʔindilag",	u"menillag",	u"nenilag"),#	light lamp
	(u"ʔumgubbat",	u"ginubat",	u"ʔiŋgubat", u"ʔiŋgubat",	u"meŋubbat",	u"neŋubat"),#	fight
	(u"ʔumhullat",	u"hinulat",	u"ʔinhulat", u"ʔinhulat",	u"menullat",	u"nenulat"),#	cover
	(u"ʔumbuŋŋet",	u"binuŋet",	u"ʔimbuŋet", None,None,None),#	scold
	(u"ʔumgalgal",	u"ginalgal",	u"ʔiŋgalgal", None,None,None),#	chew
	(u"ʔumʔagtuʔ",	u"ʔinagtuʔ",	u"ʔinʔagtuʔ", u"ʔinʔagtuʔ",	u"meŋagtuʔ",	u"neŋagtuʔ"),#	carry on head
	(u"ʔumʔehneŋ",	u"ʔinehneŋ",	u"ʔinʔehneŋ", None,None,None),#	stand
	(u"ʔumbebhat",	u"binhat",	u"ʔimbehat", None,None,None),#	cut rattan
	(u"ʔumdedʔek",	u"dinʔek",	u"ʔindeʔek", u"ʔindeʔek",	u"menʔek",	u"nenʔek"),#	accuse
	(u"ʔumtuggun",	u"sinugun",	u"ʔintugun", None,None,None),#	advise
	(u"ʔumtetpen",	u"simpen",	u"ʔintepen", u"ʔintepen",	u"mempen",	u"nempen"),#	measure
	(u"ʔumpeptut",	u"pintut",	u"ʔimpetut",None,None,None),#	dam
	(u"ʔumhehpuŋ",	u"himpuŋ",	u"ʔinhepuŋ",None,None,None),#	break a stick
	(u"ʔumtetkuk",	u"siŋkuk",	u"ʔintekuk",u"ʔintekuk",	u"meŋkuk",	u"neŋkuk"),#	shout
	(u"ʔumkekbet",	u"kimbet",	u"ʔiŋkebet",u"ʔiŋkebet",	u"meŋbet",	u"neŋbet"),#	scratch
	(u"ʔumbebdad",	u"bindad",	u"ʔimbedad",u"ʔimbedad",	u"memdad",	u"nemdad"),#	untie
	(u"ʔumdedgeh",	u"diŋgeh",	u"ʔindegeh",u"ʔindegeh",	u"meŋgeh",	u"neŋgeh"),#	sick
	
#	instrumental	contrastive	contrastive
#	past focus	id. imperfective	id. perfective
#	(u"ʔinduntuk",	u"menuntuk",	u"nenuntuk"),#	punch
#	(u"ʔimbayuʔ",	u"memayyuʔ",	u"nemayuʔ"),#	pound rice
#	(u"ʔindilag",	u"menillag",	u"nenilag"),#	light lamp
#	(u"ʔiŋgubat",	u"meŋubbat",	u"neŋubat"),#	fight
#	(u"ʔinhulat",	u"menullat",	u"nenulat"),#	cover
	(None,None,None,u"ʔintanem",	u"menannem",	u"nenanem"),#	plant
	(None,None,None,u"ʔimpedug",	u"memdug",	u"nemdug"),#	chase
#	(u"ʔimbedad",	u"memdad",	u"nemdad"),#	untie
#	(u"ʔiŋkebet",	u"meŋbet",	u"neŋbet"),#	scratch
	(None,None,None,u"ʔimbekaʔ",	u"memkaʔ",	u"nemkaʔ"),#	dig
#	(u"ʔintepen",	u"mempen",	u"nempen"),#	measure
	(None,None,None,u"ʔintebaʔ",	u"membaʔ",	u"nembaʔ"),#	kill a pig
#	(u"ʔintekuk",	u"meŋkuk",	u"neŋkuk"),#	shout
#	(u"ʔindegeh",	u"meŋgeh",	u"neŋgeh"),#	sick
	(None,None,None,u"ʔinhepaw",	u"mempaw",	u"nempaw"),#	possess
	(None,None,None,u"ʔinteled",	u"menled",	u"nenled"),#	sting
#	(u"ʔindeʔek",	u"menʔek",	u"nenʔek"),#	accuse
	(None,None,None,u"ʔinʔebaʔ",	u"meŋbaʔ",	u"neŋbaʔ"),#	carry on back
	(None,None,None,u"ʔinʔinum",	u"meŋinnum",	u"neŋinum"),#	drink
#	(u"ʔinʔagtuʔ",	u"meŋagtuʔ",	u"neŋagtuʔ"),#	carry on head
	(None,None,None,u"ʔinʔalaʔ",	u"meŋallaʔ",	u"neŋalaʔ"),#	get
	(None,None,None,u"ʔinʔawit",	u"meŋawwit",	u"neŋawit"),#	get

# The following past subject clausal focus forms involve a different prefix, using some of the roots found above. A number of roots require reduplication of the first root syllable. 

# 	nandunduntuk	‘punch’	nampepedug	‘chase’
# 	naŋkekebet	‘scratch’	nambebekaʔ	‘dig’
# 	nantetekuk	‘shout’	nandedeʔek	‘accuse
# 	nanʔeʔebaʔ	‘carry on back’	nanʔiʔinum	‘drink’
# 	nantanem	‘plant’
	]))

sevenProblems.append('''8: Kikuria
	In some (but not all) of the examples below, morphemes boundaries have been been introduced to assist in the analysis. Every noun is assigned to a grammatical class conventionally given a number (1-20), which is indicated by a particular prefix on the nouns (e.g. omo- for cl. 1); there are also pronoun prefixes on verbs marking subject and object for each class. Tones may be disregarded (however, it is predictable in the infinitive). It is important to pay attention to interaction between processes in this problem.

	ogo-táángá	‘to begin’	oko-gɛ́sa	‘to harvest’
	oko-rɔ́ga	‘to witch’	oko-réma	‘to plow’
	oko-hóórá	‘to thresh’	ugu-sííká	‘to close a door’
	ugu-súraangá	‘to sing praise’	uku-gííngá	‘to shave’
	ugu-túúhá	‘to be blunt’

	ogo-kó-bárǎ	‘to count you (sg)’	uku-gú-súraánga	‘to praise you (sg)’
	oko-mó-bárǎ	‘to count him’	uku-mú-súraánga	‘to praise him’
	ogo-tó-bárǎ	‘to count us’	ugu-tú-súraánga	‘to praise us’
	oko-gé-bárǎ	‘to count them (4)’	uku-gí-súraánga	‘to praise it (4)’
	oko-ré-bárǎ	‘to count it (5)’	uku-rí-súraánga	‘to praise it (5)’
	uku-bí-bárǎ	‘to count it (8)’	uku-bí-súraánga	‘to praise it (8)’
	uku-chí-bárǎ	‘to count it (10)’	ugu-chí-súraánga	‘to praise it (10)’

	oko-mó-gó-gɛsɛ́ra	‘to harvest it (3) for him’
	uku-mú-gú-siíkya	‘to make him close it (3)’
	uku-mú-gú-siíndya	‘to make him win it (3)’
	oko-bá-súraánga	‘to praise them’
	oko-mó-bá-suráángéra	‘to praise them for him’
	oko-bá-mú-suráángéra	‘to praise him for them’

	to V	to make to V	to V for	to make V for
	okoréma	ukurímyá	okorémérǎ	ukurímíryá	‘weed’
	okoróma	ukurúmyá	okorómérǎ	ukurúmíryá	‘bite’
	okohóórá	ukuhúúryá	okohóórérá	ukuhúúríryá	‘thresh’
	okohéétóká	ukuhíítúkyá	okohéétókerá	ukuhíítúkiryá	‘remember’
	okogéémbá	ukugíímbyá	okogéémbérá	ukugíímbíryá	‘make rain’
	ogosóóká	ugusúúkyá	ogosóókérá	ugusúúkíryá	‘respect’
	ogotégétǎ	ugutígítyǎ	ogotégéterá	ugutígítiryá	‘be late’
	okorɔ́ga	okorógyá	okorɔ́gɛ́rǎ	okorógéryá	‘bewitch’
	okogɔ́ɔ́gá	okogóógyá	okogɔ́ɔ́gɛ́rá	okogóógéryá	‘slaughter’
	okogɔ́ɔ́tá	okogóótyá	okogɔ́ɔ́tɛ́rá	okogóótéryá	‘hold’
	ogosɔ́ka	ogosókyá	ogosɔ́kɛ́rǎ	ogosókéryá	‘poke’
	ogotɛ́rɛ́kǎ	ogotérékyá	ogotɛ́rɛ́kɛrá	ogotérékeryá	‘brew’
	okogɛ́sa	okogésyá	okogɛ́sɛ́rǎ	okogéséryá	‘harvest’
	ogosɛ́ɛ́nsá	ogoséénsyá	ogosɛ́ɛ́nsɛ́rá	ogoséénséryá	‘winnow’

	to V	to make to V	to V for	to make V for
	ugusííká	ugusííkyá	ogoséékérá	ugusííkíryá	‘to close’
	ukurúga	ukurúgyá	okorógérǎ	ukurúgíryá	‘to cook’
	ugusúka	ugusúkyá	ogosókérǎ	ugusúkíryá	‘to plait’
	ukurííngá	ukurííngyá	okorééngérá	ukurííngíryá	‘to fold’
	ugusííndá	ugusííndyá	ogosééndérá	ugusííndíryá	‘to win’

	imperative	infinitive	they will V	then will V for
	remǎ	okoréma	mbareréma	mbareréméra	‘cultivate’
	barǎ	okobára	mbarebára	mbarebáréra	‘count’
	atǎ	ogɔɔ́ta	mbarɛɛ́ta	mbarɛɛ́tɛ́ra	‘be split’
	ahǎ	okɔɔ́ha	mbarɛɛ́ha	mbarɛɛ́hɛ́ra	‘pick greens’
	agǎ	okɔɔ́ga	mbarɛɛ́ga	mbarɛɛ́gɛ́ra	‘weed’
	aangá	okɔɔ́nga	mbarɛɛ́nga	mbarɛɛ́ngɛ́ra	‘refuse’
	andeká	okɔɔ́ndɛ́kǎ	mbarɛɛ́ndɛ́ka	mbarɛɛ́ndɛ́kɛra	‘write’

	imperative	3s subjunctive	3s subjunctive for
	remǎ	aremɛ̌	aremerɛ́	‘cultivate’
	tɛrɛká	atɛrɛkɛ́	atɛrɛkɛ́rɛ	‘brew’
	ebǎ	ɛɛbɛ̌	ɛɛbɛrɛ́	‘forget’
	egǎ	ɛɛgɛ̌	ɛɛgɛrɛ́	‘learn’
	ogǎ	ɔɔgɛ̌	ɔɔgɛrɛ́	‘be sharp’
	ɛyǎ	ɛɛyɛ̌	ɛɛyɛrɛ́	‘sweep’
	ɔrɔká	ɔɔrɔkɛ́	ɔɔrɔkɛ́rɛ	‘come out’
''')

sevenProblems.append(Problem('''
9: Lardil
	Account for the phonological alternations seen in the data below.
''',
#	Bare N	Accusative	Nonfuture	Future	Gloss
[                             
	(u"kentapal",	u"kentapalin",	u"kentapalŋar",	u"kentapaluṛ"),#	dugong
	(u"ketar",	u"ketarin",	u"ketarŋar",	u"ketaruṛ"),#	river
	(u"miyaṛ",	u"miyaṛin",	u"miyaṛŋar",	u"miyaṛuṛ"),#	spear
	(u"yupur",	u"yupurin",	u"yupurŋar",	u"yupuruṛ"),#	red rock cod
	(u"taŋur",	u"taŋurin",	u"taŋurŋar",	u"taŋuruṛ"),#	crab sp.
	(u"yaraman",	u"yaramanin",	u"yaramanar",	u"yaramankuṛ"),#	horse
	(u"maaṇ",	u"maaṇin",	u"maaṇar",	u"maaṇkuṛ"),#	spear
	(u"pirŋen",	u"pirŋenin",	u"pirŋenar",	u"pirŋenkuṛ"),#	woman
	(u"mela",	u"melan",	u"melaŋar",	u"melaṛ"),#	sea
	(u"tawa",	u"tawan",	u"tawaŋar", u"tawaṛ"),#	rat
	(u"wanka",	u"wankan",	u"wankaŋar",	u"wankaṛ"),#	arm
	(u"kuŋka",	u"kuŋkan",	u"kuŋkaŋar",	u"kuŋkaṛ"),#	groin
	(u"tarŋka",	u"tarŋkan", u"tarŋkaŋar", u"tarŋkaṛ"),#	barracuda
	(u"ŋuka",	u"ŋukun",	u"ŋukuŋar",	u"ŋukuṛ"),#	water
	(u"ŋuṛa",	u"ŋuṛun",	u"ŋuṛuŋar",	u"ŋuṛuṛ"),#	forehead
	(u"kaṭa",	u"kaṭun",	u"kaṭuŋar",	u"kaṭuṛ"),#	child
	(u"muṇa", u"muṇun", u"muṇuŋar", u"muṇuṛ"),#	elbow
	(u"ŋawa",	u"ŋawun",	u"ŋawuŋar",	u"ŋawuṛ"),#	wife
	(u"keṇṭe",	u"keṇṭin",	u"keṇṭiŋar",	u"keṇṭiwuṛ"),#	wife
	(u"tyimpe", u"tyimpin", u"tyimpiŋar", u"tyimpiwuṛ"),#	tail
	(u"ŋiṇe",	u"ŋiṇin",	u"ŋiṇiŋar",	u"ŋiṇiwuṛ"),#	skin
	(u"pape",	u"papin",	u"papiŋar",	u"papiwuṛ"),#	father’s mother
	(u"tyempe",	u"tyempen",	u"tyempeŋar",	u"tyempeṛ"),#	mother’s father
	(u"wiṭe",	u"wiṭen",	u"wiṭeŋar",	u"wiṭeṛ"),#	interior
	(u"waŋal",	u"waŋalkin",	u"waŋalkar",	u"waŋalkuṛ"),#	boomerang
	(u"menyel",	u"menyelkin",	u"menyelkar",	u"menyelkuṛ"),#	dogfish sp.
	(u"makar",	u"makarkin",	u"makarkar",	u"makarkuṛ"),#	anthill
	(u"yalul",	u"yalulun",	u"yaluluŋar",	u"yaluluṛ"),#	flame
	(u"mayar",	u"mayaran",	u"mayaraŋar",	u"mayaraṛ"),#	rainbow
	(u"talkur",	u"talkuran",	u"talkuraŋar",	u"talkuraṛ"),#	kookaburra
	(u"wiwal",	u"wiwalan",	u"wiwalaŋar",	u"wiwalaṛ"),#	bush mango
	(u"karikar",	u"karikarin",	u"karikariŋar",	u"karikariwuṛ"),#	butter-fish
	(u"yiliyil",	u"yiliyilin",	u"yiliyiliŋar",	u"yiliyiliwuṛ"),#	oyster sp
	(u"yukar",	u"yukarpan",	u"yukarpaŋar",	u"yukarpaṛ"),#	husband
	(u"pulŋar",	u"pulŋarpan",	u"pulŋarpaŋar", u"pulŋarpaṛ"),#	huge
	(u"wulun",	u"wulunkan",	u"wulunkaŋar",	u"wulunkaṛ"),#	fruit sp.
	(u"wuṭal",	u"wuṭaltyin",	u"wuṭaltyiŋar",	u"wuṭaltyiwur"),#	meat
	(u"kantukan",	u"kantukantun",	u"kantukantuŋar",	u"kantukantuṛ"),#	red
	(u"karwakar",	u"karwakarwan",	u"karwakarwaŋar",	u"karwakarwaṛ"),#	wattle sp.
	(u"turara",	u"turaraŋin",	u"turaraŋar",	u"turaraŋkuṛ"),#	shark
	(u"ŋalu",	u"ŋalukin",	u"ŋalukar",	u"ŋalukuṛ"),#	story
	(u"kurka",	u"kurkaŋin",	u"kurkaŋar",	u"kurkaŋkuṛ"),#	pandja
	(u"taŋku",	u"taŋkuŋin",	u"taŋkuŋar",	u"taŋkuŋkuṛ"),#	oyster sp.
	(u"kurpuṛu",	u"kurpuṛuŋin",	u"kurpuṛuŋar",	u"kurpuṛuŋkuṛ"),#	lancewood
	(u"putu",	u"putukan",	u"putukaŋar",	u"putukaṛ"),#	short
	(u"maali", u"maaliyan", u"maaliyaŋar",	u"maaliyaṛ"),#	swamp turtle
	(u"tyiṇtirpu", u"tyiṇtirpuwan",	u"tyiṇtirpuwaŋar",	u"tyiṇtirpuwaṛ"),#	willie wagtail
	(u"pukatyi", u"pukatyiyan",	u"pukatyiyaŋar",	u"pukatyiyaṛ"),#	hawk sp.
	(u"murkuni",	u"murkuniman",	u"murkunimaŋar",	u"murkunimaṛ"),#	nullah
	(u"ŋawuŋa",	u"ŋawuŋawun",	u"ŋawuŋawuŋar",	u"ŋawuŋawuṛ"),#	termite
	(u"tipiti",	u"tipitipin",	u"tipitipiŋar",	u"tipitipiwuṛ"),#	rock-cod sp.
	(u"tapu",	u"taputyin",	u"taputyiŋar",	u"taputyiwuṛ"),#	older brother
	(u"muŋkumu",	u"muŋkumuŋkun",	u"muŋkumuŋkuŋar",	u"muŋkumuŋkuṛ"),#	wooden axe
	(u"tyumputyu",	u"tyumputyumpun",	u"tyumputyumpuŋar",	u"tyumputyumpuṛ")#	dragonfly
    ]))
	
sevenProblems.append(Problem('''10: Sakha (Yakut)
	Give a phonological analysis to the following case-marking paradigms of nouns in Sakha.
''',
#	noun	plural	associative	gloss
[
	(u"aɣa",	u"aɣalar",	u"aɣalɨɨn"),#	father
	(u"paarta",	u"paartalar",	u"paartalɨɨn"),#	school desk
	(u"tɨa",	u"tɨalar",	u"tɨalɨɨn"),#	forest
	(u"kinige",	u"kinigeler",	u"kinigeliin"),#	book
	(u"šie",	u"šieler",	u"šieliin"),#	house
	(u"iye",	u"iyeler",	u"iyeliin"),#	mother
	(u"kini",	u"kiniler",	u"kiniliin"),#	3rd person
	(u"bie",	u"bieler",	u"bieliin"),#	mare
	(u"oɣo",	u"oɣolor",	u"oɣoluun"),#	child
	(u"Xopto",	u"Xoptolor",	u"Xoptoluun"),#	gull
	(u"börö",	u"börölör",	u"börölüün"),#	wolf
	(u"tɨal",	u"tɨallar",	u"tɨallɨɨn"),#	wind
	(u"ɨal",	u"ɨallar",	u"ɨallɨɨn"),#	neighbor 
	(u"kuul",	u"kuullar",	u"kuulluun"),#	sack
	(u"at",	u"attar",	u"attɨɨn"),#	horse
	(u"balɨk",	u"balɨktar",	u"balɨktɨɨn"),#	fish
	(u"ɨskaap",	u"ɨskaaptar",	u"ɨskaaptɨɨn"),#	cabinet
	(u"oɣus",	u"oɣustar",	u"oɣustuun"),#	bull
	(u"kus",	u"kustar",	u"kustuun"),#	duck
	(u"tünnük",	u"tünnükter",	u"tünnüktüün"),#	window
	(u"sep",	u"septer",	u"septiin"),#	tool
	(u"et",	u"etter",	u"ettiin"),#	meat
	(u"örüs",	u"örüster",	u"örüstüün"),#	river
	(u"tiis",	u"tiister",	u"tiistiin"),#	tooth
	(u"soroX",	u"soroXtor",	u"soroXtuun"),#	some person
	(u"oX",	u"oXtor",	u"oXtuun"),#	arrow
	(u"oloppos",	u"oloppostor",	u"oloppostuun"),#	chair
	(u"ötöX",	u"ötöXtör",	u"ötöXtüün"),#	abandoned farm
	(u"ubay",	u"ubaydar",	u"ubaydɨɨn"),#	elder brother
	(u"saray",	u"saraydar",	u"saraydɨɨn"),#	barn
	(u"tɨy",	u"tɨydar",	u"tɨydɨɨn"),#	foal
	(u"atɨɨr",	u"atɨɨrdar",	u"atɨɨrdɨɨn"),#	stallion
	(u"oyuur",	u"oyuurdar",	u"oyuurduun"),#	forest
	(u"üčügey",	u"üčügeyder",	u"üčügeydiin"),#	good person
	(u"ešiiy",	u"ešiiyder",	u"ešiiydiin"),#	elder sister
	(u"tomtor",	u"tomtordor",	u"tomtorduun"),#	knob
	(u"moɣotoy",	u"moɣotoydor",	u"moɣotoyduun"),#	chipmunk
	(u"kötör",	u"kötördör",	u"kötördüün"),#	bird
	(u"bölköy",	u"bölköydör",	u"bölköydüün"),#	islet
	(u"Xatɨŋ",	u"Xatɨŋnar",	u"Xatɨŋnɨɨn"),#	birch
	(u"aan",	u"aannar",	u"aannɨɨn"),#	door
	(u"tiiŋ",	u"tiiŋner",	u"tiiŋniin"),#	squirrel
	(u"sordoŋ",	u"sordoŋnor",	u"sordoŋnuun"),#	pike
	(u"olom",	u"olomnor",	u"olomnuun"),#	ford
	(u"oron",	u"oronnor",	u"oronnuun"),#	bed
	(u"bödöŋ",	u"bödöŋnör",	u"bödöŋnüün"),#	strong one
]))	
	# noun	partitive	comparative	ablative	gloss
	# aɣa	aɣata	aɣataaɣar	aɣattan	father
	# paarta	paartata	paartataaɣar	paartattan	school desk
	# tɨa	tɨata	tɨataaɣar	tɨattan	forest
	# kinige	kinigete	kinigeteeɣer	kinigetten	book
	# š̌ie	š̌iete	š̌ieteeɣer	š̌ietten	house
	# iye	iyete	iyeteeɣer	iyetten	mother
	# kini	kinite	kiniteeɣer	kinitten	3rd person
	# bie	biete	bieteeɣer	bietten	mare
	# oɣo	oɣoto	oɣotooɣor	oɣotton	child
	# Xopto	Xoptoto	Xoptotooɣor	Xoptotton	gull
	# börö	börötö	börötööɣör	böröttön	wolf
	# tɨal	tɨalla	tɨallaaɣar	tɨaltan	wind
	# ɨal	ɨalla	ɨallaaɣar	ɨaltan	neighbor
	# kuul	kuulla	kuullaaɣar	kuultan	sack
	# moXsoɣol	moXsoɣollo	moXsoɣollooɣor	moXsoɣolton	falcon
	# at	atta	attaaɣar	attan	horse
	# balɨk	balɨkta	balɨktaaɣar	balɨktan	fish
	# ɨskaap	ɨskaapta	ɨskaaptaaɣar	ɨskaaptan	cabinet
	# oɣus	oɣusta	oɣustaaɣar	oɣustan	bull
	# kus	kusta	kustaaɣar	kustan	duck
	# tünnük	tünnükte	tünnükteeɣer	tünnükten	window
	# sep	septe	septeeɣer	septen	tool
	# et	ette	etteeɣer	etten	meat
	# örüs	örüste	örüsteeɣer	örüsten	river
	# tiis	tiiste	tiisteeɣer	tiisten	tooth
	# soroX	soroXto	soroXtooɣor	soroXton	some person
	# ötöX	ötöXtö	ötöXtööɣör	ötöXtön	abandoned farm
	# ubay	ubayda	ubaydaaɣar	ubaytan	elder brother
	# saray	sarayda	saraydaaɣar	saraytan	barn
	# tɨy	tɨyda	tɨydaaɣar	tɨytan	foal
	# atɨɨr	atɨɨrda	atɨɨrdaaɣar	atɨɨrtan	stallion
	# Xirur	Xirurda	Xirurdaaɣar	Xirurtan	surgeon
	# üčügey	üčügeyde	üčügeydeeɣer	üčügeyten	good person
	# tomtor	tomtordo	tomtordooɣor	tomtorton	knob
	# moɣotoy	moɣotoydo	moɣotoydooɣor	moɣotoyton	chipmunk
	# kötör	kötördö	kötördööɣör	kötörtön	bird
	# suorɣan	suorɣanna	suorɣannaaɣar	suorɣantan	blanket
	# Xatɨŋ	Xatɨŋna	Xatɨŋnaaɣar	Xatɨŋtan	birch
	# aan	aanna	aannaaɣar	aantan	door
	# tiiŋ	tiiŋne	tiiŋneeɣer	tiiŋten	squirrel
	# sordoŋ	sordoŋno	sordoŋnooɣor	sordoŋton	pike
	# olom	olomno	olomnooɣor	olomton	ford
	# bödöŋ	bödöŋnö	bödöŋnööɣör	bödöŋtön	strong one
	
	# noun	dative	accusative	gloss
	# aɣa	aɣaɣa	aɣanɨ	father
	# š̌ie	š̌ieɣe	š̌ieni	house
	# iye	iyeɣe	iyeni	mother
	# oɣo	oɣoɣo	oɣonu	child
	# börö	böröɣö	börönü	wolf
	# tɨal	tɨalga	tɨalɨ	wind
	# kuul	kuulga	kuulu	sack
	# at	akka	atɨ	horse
	# balɨk	balɨkka	balɨgɨ	fish
	# ɨskaap	ɨskaapka	ɨskaabɨ	cabinet
	# oɣus	oɣuska	oɣuhu	bull
	# kus	kuska	kuhu	duck
	# sep	sepke	sebi	tool
	# et	ekke	eti	meat
	# tiis	tiiske	tiihi	tooth
	# ot	okko	otu	grass
	# soroX	soroXXo	soroɣu	some person
	# ötöX	ötöXXö	ötöɣü	abandoned farm
	# oX	oXXo	oɣu	arrow
	# saray	sarayga	sarayɨ	barn
	# tɨy	tɨyga	tɨyɨ	foal
	# kötör	kötörgö	kötörü	bird

	# oyuun	oyuuŋŋa	oyuunu	shaman
	# Xatɨŋ	Xatɨŋŋa	Xatɨŋɨ	birch
	# aan	aaŋŋa	aanɨ	door
	# olom	olomŋo	olomu	ford
	
	# noun	ourN	gloss	noun	our N	gloss
	# aɣa	aɣabɨt	father	iye	iyebit	mother
	# uol	uolbut	son	kötör	kötörbüt	bird
	# kɨlaas	kɨlaaspɨt	classroom	ɨskaap	ɨskaappɨt	cabinet
	# kuorat	kuorappɨt	town	tiis	tiispit	tooth
	# ohoX	ohoXput	stove	tünnük	tünnükpüt	window
	# aan	aammɨt	door	kapitan	kapitammɨt	capitain
	# tiiŋ	tiiŋmit	squirrel	oron	orommut	bed
	# kün	kümmüt	day
sevenProblems.append(Problem('''	
11: Sadzava Ukrainian
Sadžava Ukrainian
	Give a phonological analysis of the following data. Assume that all surface occurrences of ky and gy in this language are derived by rule. Also assume that stress is located on the proper vowel in the underlying representation: the rules for shifting stress are too complex to be considered here. Nouns in declension II depalatalizes a consonant before the locative suffix, and nouns in declension III depalatalize in the genitive. The variation in the genitive and locative sg. suffix in declension I (-i or -a versus -u) is lexically governed: do not write rules which select between these suffixes. Concentrate on extablishing the correct underlying representations for the noun stem.
''',[
#	Declension I
#	Nom. sg.	Gen. sg.	Loc. sg.	Gloss
    (u"plást",	u"plastá",	u"plasykyí",None,None,None,None,None),#	layer
	(u"skorúx",	u"skoruxá",	u"skorusyí",None,None,None,None,None),#	mountain ash
	(u"ɣyryíx",	u"ɣyryixá",	u"ɣyryisyí",None,None,None,None,None),#	sin
	(u"pastúx",	u"pastuxá",	u"pastusyí",None,None,None,None,None),#	herdsman
	(u"mynyúx",	u"mynyúxa",	u"mynyúsyi",None,None,None,None,None),#	fish sp.
	(u"plúɣ",	u"plúɣa",	u"plúzyi",None,None,None,None,None),#	plow
	(u"sytyíɣ",	u"stóɣa",	u"stózyi",None,None,None,None,None),#	stack
	(u"sák",	u"sáka",	u"sátsyi",None,None,None,None,None),#	fishnet
	(u"bék",	u"bəká",	u"bətsyí",None,None,None,None,None),#	bull
	(u"lést",	u"ləstá",	u"ləsykyí",None,None,None,None,None),#	letter
	(u"lést",	u"lésta",	u"lésykyi",None,None,None,None,None),#	leaf
	(u"pylyít",	u"plóta",	u"plókyi",None,None,None,None,None),#	wicker fence
	(u"symyryíd",	u"smróda",	u"smrógyi",None,None,None,None,None),#	stench
	(u"fyíst",	u"fostá",	u"fosykyí",None,None,None,None,None),#	tail
	(u"myíst",	u"mósta",	u"mósykyi",None,None,None,None,None),#	bridge
	(u"lyíd",	u"lǽdu",	u"lədú",None,None,None,None,None),#	ice
	(u"dyryít",	u"dróta",	u"drókyi",None,None,None,None,None),#	thick wire
	(u"myíd",	u"mǽdu",	u"mədú",None,None,None,None,None),#	honey
	(u"vyíl",	u"volá",	u"volyí",None,None,None,None,None),#	ox
	(u"vyíz",	u"vóza",	u"vózyi",None,None,None,None,None),#	cart
	(u"sér",	u"séra",	u"séryi",None,None,None,None,None),#	cottage cheese
	(u"synyíp",	u"snopá",	u"snopyí",None,None,None,None,None),#	sheaf
	(u"ɣréb",	u"ɣrəbá",	u"ɣrəbyí",None,None,None,None,None),#	mushroom
	(u"lǽbyid",	u"lǽbəda",	u"lǽbəgyi",None,None,None,None,None),#	swan
	(u"bǽryiɣ",	u"bǽrəɣa",	u"bǽrəzyi",None,None,None,None,None),#	shore
	(u"pəryíɣ",	u"pəróɣa",	u"pərózyi",None,None,None,None,None),#	dumpling
	(u"poryíɣ",	u"poróɣa",	u"porózyi",None,None,None,None,None),#	threshhold
	(u"bolyék",	u"bolyəká",	u"bolyətsyí",None,None,None,None,None),#	abcess
	(u"vóryiɣ",	u"vóroɣa",	u"vórozyi",None,None,None,None,None),#	enemy
	(u"kónək",	u"kónəka",	u"kónətsyi",None,None,None,None,None),#	grasshopper
	(u"pótyik",	u"potóka",	u"potótsyi",None,None,None,None,None),#	stream
	(u"tyík",	u"tóka",	u"tótsyi",None,None,None,None,None),#	current
	(u"kyíl",	u"kolá",	u"kolyí",None,None,None,None,None),#	stake

#	Declension II
#	Nom. sg.	Gen. sg.	Loc. sg.	Gloss
	(None,None,None,u"kovály",	u"kovalyé",	u"kovalé",None,None),#	blacksmith
	(None,None,None,u"ǰmyíly",	u"ǰmyilyé",	u"ǰmyilé",None,None),#	bumblebee
	(None,None,None,u"kyryíly",	u"kyryilyé",	u"kyryilé",None,None),#	rabbit
	(None,None,None,u"učétəly",	u"učétəlyə",	u"učétələ",None,None),#	teacher
	(None,None,None,u"grǽbyiny",	u"grǽbənyə",	u"grǽbənə",None,None),#	comb
	(None,None,None,u"óləny", u"ólənyə", u"ólənə",None,None),#	deer
	(None,None,None,u"yačymyíny",	u"yačmǽnyə",	u"yačmǽnə",None,None),#	barley
	(None,None,None,u"yásyiny",	u"yásənyə",	u"yásənə",None,None),#	ash tree
	(None,None,None,u"zyéky",	u"zyékyə",	u"zyétə",None,None),#	son-in-law

#	Declension III
#	Nom. sg.	Gen. sg.	Gloss
	(None,None,None,None,None,None,u"másyky",	u"mástə"),#	u"fat"),#
	(None,None,None,None,None,None,u"symyíryky",	u"smǽrtə"),#,	u"death"),#
	(None,None,None,None,None,None,u"vyísyky",	u"vyístə"),#,	u"news"),#
	(None,None,None,None,None,None,u"rágyisyky",	u"rádostə"),#,	u"joy"),#
	(None,None,None,None,None,None,u"syíly",	u"sólə"),#,	u"salt"),#
	(None,None,None,None,None,None,u"póšyisyky",	u"póšəstə"),#,	u"epidemic"),#
	(None,None,None,None,None,None,u"zámyiky",	u"zámətə"),#,	u"snowstorm"),#
	(None,None,None,None,None,None,u"skátəryky",	u"skátərtə"),#,	u"tablecloth"),#
	(None,None,None,None,None,None,u"kyísyky",	u"kóstə"),#,	u"bone"),#
]))
if False:
    sevenProblems.append(Problem('''
12:	Koromfe
	Koromfe has two kinds of vowels, [-ATR] ɩʊɛɔa and [+ATR] iueoʌ. Provide an analysis of the alternations in the following data, which involve singular and plural forms of nouns and different tense-inflections for verbs.
''',[
#	Singular	Plural		gloss
	(u"gɩbrɛ",	u"gɩba",None,None,None),#		hatchet
	(u"hubre",	u"hubʌ",None,None,None),#		ditch
	(u"nɛbrɛ",	u"nɛba",None,None,None),#		pea
	(u"dĩŋgre",	u"dĩŋgʌ",None,None,None),#		bush type
	(u"zoŋgre",	u"zoŋgʌ",None,None,None),#		wing
	(u"lɔ̃ŋgrɛ",	u"lɔ̃ŋga",None,None,None),#		shoe
	(u"hullre",	u"hullʌ",None,None,None),#		gutter
	(u"sɛkrɛ",	u"sɛka",None,None,None),#		half
	(u"tɛfrɛ",	u"tɛfa",None,None,None),#		cotton fiber
	(u"dabɛɛrɛ",	u"dabɛɛya",None,None,None),#		camp
	(u"dɔɔrɛ",	u"dɔɔya",None,None,None),#		long
	(u"gɩgaarɛ",	u"gɩgaaya",None,None,None),#		vulture
	(u"pʊpaarɛ",	u"pʊpaaya",None,None,None),#		grass type
	(u"koire",	u"koyʌ",None,None,None),#		bracelet
	(u"dʊmdɛ",	u"dʊma",None,None,None),#		lion
	(u"hulomde",	u"hulomʌ",None,None,None),#		marrow
	(u"tɛmdɛ",	u"tɛma",None,None,None),#		beard
	(u"logomde",	u"logomʌ",None,None,None),#		camel
	(u"bɩndɛ",	u"bɩna",None,None,None),#		heart
	(u"hɔ̃ndɛ",	u"hɔ̃na",None,None,None),#		hoe
	(u"honde",	u"honʌ",None,None,None),#		bean
	(u"geŋde",	u"geŋʌ",None,None,None),#		pebble
	(u"zɛŋdɛ",	u"zɛŋa",None,None,None),#		upper arm
	(u"bɛllɛ",	u"bɛla",None,None,None),#		back
	(u"yɩllɛ",	u"yɩla",None,None,None),#		horn
	(u"selle",	u"selʌ",None,None,None),#		space
	(u"pallɛ",	u"pala",None,None,None),#		stretcher
	(u"deŋgele",	u"deŋgelʌ",None,None,None),#		open area
	(u"sembele",	u"sembelʌ",None,None,None),#		piece
	(u"dãɩ̃nɛ",	u"dãỹã",None,None,None),#		wood
	(u"hʊ̃ɩ̃nɛ",	u"hʊ̃ỹã",None,None,None),#		caterpillar
	(u"kɔ̃ɩ̃nɛ",	u"kɔ̃ỹã",None,None,None),#		squirrel
	(u"kɔ̃ɔ̃nɛ",	u"kɔ̃ɔ̃ỹã",None,None,None),#		old
	(u"sɔ̃ɔ̃nɛ",	u"sɔ̃ɔ̃ỹã",None,None,None),#		period
	(u"bɛtɛ",	u"bɛra",None,None,None),#		male animal
	(u"datɛ",	u"dara",None,None,None),#		chest
	(u"gete",	u"gerʌ",None,None,None),#		forked stick
	(u"gote",	u"gorʌ",None,None,None),#		stream
	(u"bɩtɛ",	u"bɩra",None,None,None),#		frog
	(u"dɔtɛ",	u"dɔra",None,None,None),#		cloud
	
#	neutral	past	progressive	gloss
	(None,None,u"ta",	u"taɛ",	u"taraa"),#	shoot
	(None,None,u"gɔ",	u"gɔɛ",	u"gɔraa"),#	go back
	(None,None,u"kʊ",	u"kɔɛ",	u"kʊraa"),#	kill
	(None,None,u"tu",	u"toe",	u"turʌʌ"),#	coat
	(None,None,u"li",	u"lee",	u"lirʌʌ"),#	forget
	(None,None,u"dɩ",	u"dɛ",	u"dɩraa"),#	eat
	(None,None,u"tã",	u"tãɛ̃",	u"tãnaa"),#	contradict
	(None,None,u"nɛ̃",	u"nɛ̃",	u"nɛ̃naa"),#	defecate
	(None,None,u"saɩ",	u"sayɛ",	u"saɩraa"),#	separate
	(None,None,u"yɛɩ",	u"yɛyɛ",	u"yɛɩraa"),#	waste
	(None,None,u"sɔɩ",	u"sɔyɛ",	u"sɔɩraa"),#	split
	(None,None,u"ỹɛ̃ɩ̃",	u"ỹɛ̃ỹɛ̃",	u"ỹɛ̃ɩ̃naa"),#	catch
	(None,None,u"dɔ̃ɩ̃",	u"dɔ̃ỹɛ̃",	u"dɔ̃ɩ̃naa"),#	dream
	(None,None,u"kɛndɩ",	u"kɛndɛ",	u"kɛndraa"),#	finish
	(None,None,u"kɛ̃sɩ",	u"kɛ̃sɛ",	u"kɛ̃sraa"),#	surpass
	(None,None,u"kɛtɩ",	u"kɛtɛ",	u"kɛtraa"),#	open
	(None,None,u"tɛŋgɩ",	u"tɛŋgɛ",	u"tɛŋgraa"),#	accompany
	(None,None,u"yisi",	u"yise",	u"yisrʌʌ"),#	suffice
	(None,None,u"yɩsɩ",	u"yɩsɛ",	u"yɩsraa"),#	draw water
	(None,None,u"birgi",	u"birge",	u"birgrʌʌ"),#	blacken
	(None,None,u"pasgɩ",	u"pasgɛ",	u"pasgraa"),#	split
	(None,None,u"mɛntɩ",	u"mɛntɛ",	u"mɛntraa"),#	assemble
	(None,None,u"gondu",	u"gonde",	u"gondrʌʌ"),#	depart
	(None,None,u"hɔ̃ŋgʊ",	u"hɔ̃ŋgɛ",	u"hɔ̃ŋgraa"),#	point
	(None,None,u"sʊrgʊ",	u"sʊrgɛ",	u"sʊrgraa"),#	drop
	(None,None,u"hɔ̃kʊ",	u"hɔ̃kɛ",	u"hɔ̃kraa"),#	scratch
	(None,None,u"zullu",	u"zulle",	u"zullrʌʌ"),#	bow
	(None,None,u"sɩbʊ",	u"sɩbɛ",	u"sɩbraa"),#	die
	(None,None,u"zambʊ",	u"zambɛ",	u"zambraa"),#	deceive
	(None,None,u"wufu",	u"wufe",	u"wufrʌʌ"),#	borrow
	(None,None,u"zɩgamsʊ",	u"zɩgamsɛ",	u"zɩgamsraa"),#	be dirty
	(None,None,u"hɛ̃msʊ",	u"hɛ̃msɛ",	u"hɛ̃msraa"),#	meet
	(None,None,u"leli",	u"lele",	u"lellʌʌ"),#	sing
	(None,None,u"pɩlɩ",	u"pɩlɛ",	u"pɩllaa"),#	trample flat
	(None,None,u"tarɩ",	u"tarɛ",	u"tataa"),#	plaster
	(None,None,u"fɛrɩ",	u"fɛrɛ",	u"fɛtaa"),#	cultivate
	(None,None,u"tʊrʊ",	u"tʊrɛ",	u"tʊtaa"),#	introduce
]))


nineProblems = [
# Problem('''
# 1.	Slovak
# 	The focus of this problem is the underlying representation of diphthongs. Discuss the underlying status of diphthongs in Slovak, based on these data. Nouns in Slovak come in three genders, which determines what suffix if any is used in the nominative singular: masculines have no suffix, feminines have -a, and neuters have -o.

# A.	There is a process of lengthening which takes place in certain morphological contexts, including the genitive plural and the diminutive.
# ''',
# #	nom. sg	gen. pl.
        
# 	lipa	li:p	‘linden tree’
# 	muxa	mu:x	‘fly’
# 	lopata	lopa:t	‘shovel’
# 	sr̩na	sr̩:n	‘deer’
# 	žena	žien	‘woman’
# 	kazeta	kaziet	‘box’
# 	hora	huor	‘forest’
# 	sirota	siruot	‘orphan’
# 	pæta	piat	‘heel’
# 	mæta	miat	‘mint’
# 	kopito	kopi:t	‘hoof’
# 	bruxo	bru:x	‘belly’
# 	blato	bla:t	‘mud’
# 	salto	sa:lt	‘somersault’
# 	embargo	emba:rg	‘embargo’
# 	yabl̩ko	yabl̩:k	‘apple’
# 	koleso	kolies	‘wheel’
# 	lono	luon	‘lap’
# 	hovædo	hoviad	‘beast’
# 	vla:da	vla:d	‘government’
# 	blu:za	blu:z	‘blouse’
# 	dla:to	dla:t	‘chisel’
# 	vi:no	vi:n	‘vine’
# 	čiara	čiar	‘line’
# 	hniezdo	hniezd	‘nest’

# 	noun	diminutive
# 	hrad	hra:dok	‘castle’
# 	list	li:stok	‘leaf’
# 	xl̩p	xl̩:pok	hair’
# 	kvet	kvietok	flower’
# 	hovædo	hoviadok	‘beast’

# B.	There is also a shortening rule that applies in certain morphological contexts, including the imperfective of verbs and the comparative of adjectives.

# 	perfective	imperfective
# 	odli:sity	odlisovaty	‘to distinguish’
# 	ku:pity	kupovaty	‘to buy’
# 	ohla:sity	ohlasovaty	‘to announce’
# 	predl̩:žity	predl̩zovaty	‘to extend’
# 	oblietaty	obletovaty	‘to fly around’
# 	uviazaty	uvæzovaty	‘to bind’

# 	adjective	comparative
# 	bli:ski	blišši:	‘near’
# 	u:ski	ušši:	‘narrow’
# 	kra:tki	kratši:	‘short’
# 	bieli	belši:	‘white’
# 	rietki	retši:	‘rare’

# C.	There is an alternation in the form of case suffixes which is governed by properties of the stem which precedes

# 	nom. sg.	gen. sg.	nom. pl.	dat. pl.	loc. pl.
# 	mesto	mesta	mesta:	mesta:m	mesta:x	‘town’
# 	blato	blata	blata:	blata:m	blata:x	‘mud’
# 	hovædo	hovæda	hovæda:	hovæda:m	hovæda:x	‘town’
# 	pi:smeno	pi:smena	pi:smena:	pi:smena:m	pi:smena:x	‘letter’
# 	za:meno	za:mena	za:mena:	za:mena:m	za:mena:x	‘pronoun’
# 	dla:to	dla:ta	dla:ta	dla:tam	dla:tax	‘town’
# 	vi:no	vi:na	vi:na	vi:nam	vi:nax	‘wine’
# 	hniezdo	hniezda	hniezda	hniezdam	hniezdax	‘nest’

# D.	The rule that explains the alternations in C also explains why a rule motivated by the data in A seems not to have applied.

# 	nom. sg.	gen. pl.
# 	za:hrada	za:hrad	‘garden’
# 	ni:žina	ni:žin	‘hollow’
# 	za:toka	za:tok	‘inlet’
# 	pi:smeno	pi:smen	‘letter’
# 	za:meno	za:men	‘pronoun’
# 	liečivo	liečiv	‘drug’

# E.	Some stems underlyingly end with consonant clusters, and undergo a process of vowel epenthesis that eliminates certain kinds of consonant clusters.

# 	nom. sg	gen. pl.
# 	ikra	ikier	‘roe’	(cf. also ikernati: ‘abounding in roe’)
# 	ihla	ihiel	‘needle’
# 	dogma	dogiem	‘dogma’
# 	sosna	sosien	‘pine tree’
# 	bedro	bedier	‘hip’
# 	radlo	radiel	‘plow’
# 	hradba	hradieb	‘rampart’
# 	doska	dosiek	‘board’
# 	kri:dlo	kri:del	‘wing’
# 	či:slo	či:sel	‘number’
# 	pa:smo	pa:sem	‘zone’
# 	vla:kno	vla:ken	‘fiber’
# 	pla:tno	pla:ten	‘linen’
# ''')]
]


MATRIXPROBLEMS = underlyingProblems + interactingProblems + sevenProblems

if __name__ == "__main__":
    from utilities import *
    for j,p in enumerate(MATRIXPROBLEMS):
        print "Problem index",j
        if isinstance(p,Problem):
            print p.description
        else: continue
        
        print
        if p.parameters is not None: continue
        
        for ss in p.data:
            print u" ~ ".join(s for s in ss if s is not None)
            try:
                a = runWithTimeout(lambda: minimumCostAlignment([tokenize(s) for s in ss if s is not None ]),
                                   1.)
                print "\t",a[0].ur()
            except RunWithTimeout: print("TIMEOUT")
