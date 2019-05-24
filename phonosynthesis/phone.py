class Phone(dict):
    '''A representation of a single speech sound'''
    def __init__(self, symbols):
        self._symbols = symbols
    def __str__(self):
        return ''.join(self._symbols)
