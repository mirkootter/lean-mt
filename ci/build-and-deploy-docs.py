from os import system, environ
import pathlib
import shutil
from subprocess import check_output, run

REPO = 'git@github.com:mirkootter/lean-mt-doc.git'

short_hash = check_output(['git', 'rev-parse', '--short', 'HEAD']).decode('utf-8').strip()
print("Current repository hash:", short_hash)

commit_message = f"Update to {short_hash}"

check_output(['git', 'clone', '--bare', REPO])

last_commit = check_output(['git', 'log', '-1', '--pretty=format:%s'], cwd='lean-mt-doc.git').decode('utf-8')
shutil.rmtree('lean-mt-doc.git')

if last_commit == commit_message:
    print("Already up to date")
    exit()

lake = pathlib.Path.home() / '.elan' / 'bin' / 'lake';

print("Build documentation")
run([lake, 'build', '-Kenv=dev', 'Mt:docs'], check = True)
run([lake, 'build', '-Kenv=dev', 'Samples:docs'], check = True)

print("Deploy")
run(['git', 'init', '-b', 'main'], cwd='build/doc', check = True)
run(['git', 'config', 'user.name', 'lean-mt-bot'], cwd='build/doc', check = True)
run(['git', 'config', 'user.email', ''], cwd='build/doc', check = True)
run(['git', 'add', '-A'], cwd='build/doc', check = True)
run(['git', 'commit', '-m', commit_message], cwd='build/doc', check = True)
run(['git', 'remote', 'add', 'origin', REPO], cwd='build/doc', check = True)
run(['git', 'push', '-f', 'origin', 'main'], cwd='build/doc', check = True)