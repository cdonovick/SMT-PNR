from setuptools import setup
setup(
        name='pnrdoctor',
        version='0.1',
        description='SMT based place and route tool',
        author='Caleb Donovick, Makai Mann',
        author_email='donovick@cs.stanford.edu',
        license='MIT',
        packages=['pnrdoctor'],
        install_requires=['coreir', 'monosat>=1.4',], #should inculde smt-switch
        python_requires='>=3.6'
)

