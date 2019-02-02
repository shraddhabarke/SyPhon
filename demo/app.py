#!/usr/bin/env python3

from flask import Flask, abort, jsonify, request
from demo import ipa_data, phonosynth

app = Flask(__name__, static_url_path='')

@app.route('/')
def handle_homepage():
  return app.send_static_file('index.html')

@app.route('/api/infer_rule', methods=['POST'])
def handle_infer_rule():
  if not request.json or not 'wordStems' in request.json:
    abort(400)

  words = []
  for stem in request.json['wordStems']:
    words.append((stem['underlyingForm'], stem['realization']))

  return jsonify(infer_rule(words))

def format_features(features):
  symbol = ipa_data.FEATURES_TO_LETTERS.get(frozenset(features.items()))
  if symbol:
    return symbol
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

if __name__ == '__main__':
  app.run()
