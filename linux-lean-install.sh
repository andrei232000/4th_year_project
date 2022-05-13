curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

python3 -m pip install --user pipx
python3 -m pipx ensurepath
source ~/.profile
pipx install mathlibtools