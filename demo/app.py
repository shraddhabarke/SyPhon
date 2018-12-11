#!/usr/bin/env python3
from flask import Flask, abort, jsonify, request
from demo import phonosynth

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
  symbol = phonosynth.FEATURES_TO_SYMBOL.get(frozenset(features.items()))
  if symbol:
    return symbol
  else:
    return [{'feature': feature, 'positive': value == '+'} for feature, value in features.items()]

def infer_rule(words):
  data = phonosynth.parse(words)
  change = phonosynth.infer_change(data)
  left, phone, right = phonosynth.infer_rule(data)
  
  return {
    'phone': format_features(phone),
    'change': format_features(change),
    'context': {
      'left': format_features(left),
      'right': format_features(right)
    }
  }
