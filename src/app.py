from flask import Flask, abort, jsonify, request, render_template
from . import ipa_data, phonosynth

app = Flask(__name__, static_url_path='')

@app.route('/')
def handle_homepage():
  return render_template('index.html')

@app.route('/api/infer_rule', methods=['POST'])
def handle_infer_rule():
  if not request.json or not 'wordStems' in request.json:
    abort(400)

  words = []
  for stem in request.json['wordStems']:
    words.append((stem['underlyingForm'], stem['realization']))

  return jsonify(infer_rule(words))

def format_features(features):
  matching_letter = ipa_data.get_matching_letter(features)
  if matching_letter:
    return matching_letter
  elif len(features) == 0:
    return None
  else:
    return [{'feature': feature, 'positive': value == '+'} for feature, value in features.items()]

def infer_rule(words):
  data = phonosynth.parse(words)
  changes = phonosynth.infer_change(data)
  rules = phonosynth.infer_rule(data, changes)
  response = []
  for rule in rules:
    if rule:
      change, (left, phone, right) = rule
      response.append({
        'target': format_features(phone),
        'change': format_features(change),
        'context': {
          'left': format_features(left),
          'right': format_features(right)
        }
      })
  return response
