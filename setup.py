from setuptools import setup, find_packages

setup(
  name='phonosynthesis',
  version='0.1.0',
  packages=find_packages(),
  python_requires='~=3.6',
  install_requires=[
    'flask~=1.0',
  ],

  # TODO: Update this with actual entry points for cmdline tools
  entry_points={},

  project_urls={
    'Demo': 'https://goto.ucsd.edu/phonosynth',
    'Source': 'https://github.com/shraddhabarke/Phonosynthesis',
  },
)
