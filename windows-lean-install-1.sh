git config --global core.autocrlf input

curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

'PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.profile"