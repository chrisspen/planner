import os

from setuptools import setup, find_packages, Command

import planner

CURRENT_DIR = os.path.abspath(os.path.dirname(__file__))

def get_reqs(*fns):
    lst = []
    for fn in fns:
        for package in open(os.path.join(CURRENT_DIR, fn)).readlines():
            package = package.strip()
            if not package:
                continue
            lst.append(package.strip())
    return lst

class TestCommand(Command):
    description = "Runs unittests."
    user_options = []
    def initialize_options(self):
        pass
    def finalize_options(self):
        pass
    def run(self):
        os.system('tox')

setup(
    name="planner",
    version=planner.__version__,
    packages=find_packages(),
    author="Chris Spencer",
    author_email="chrisspen@gmail.com",
    description="A simple Python real-time best-first planning algorithm.",
    license="LGPL",
    url="https://github.com/chrisspen/planner",
    classifiers=[
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
    package_data={
        'planner': [
            'tests/*/*/*.*',
        ],
    },
    zip_safe=False,
    install_requires=get_reqs('requirements.txt'),
    tests_require=get_reqs('requirements-test.txt'),
)
