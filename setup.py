from setuptools import setup, find_packages, Command

import os
import urllib

import planner

class TestCommand(Command):
    description = "Runs unittests."
    user_options = []
    def initialize_options(self):
        pass
    def finalize_options(self):
        pass
    def run(self):
        os.system('cd planner; ./test.sh')
        
setup(
    name = "planner",
    version = planner.__version__,
    packages = find_packages(),
    author = "Chris Spencer",
    author_email = "chrisspen@gmail.com",
    description = "A simple Python real-time best-first planning algorithm.",
    license = "LGPL",
    url = "https://github.com/chrisspen/planner",
    classifiers = [
        'Development Status :: 3 - Alpha',
        'Intended Audience :: Developers',
        'Intended Audience :: Science/Research',
        'Topic :: Scientific/Engineering :: Artificial Intelligence',
        'License :: OSI Approved :: LGPL License',
        'Operating System :: OS Independent',
        'Programming Language :: Python',
    ],
    cmdclass={
        'test': TestCommand,
    },
)