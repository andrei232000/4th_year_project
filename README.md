Instructions for installing Lean and compiling the project
==========================================================


Scripts
-------
This is an explanation of the included script files in relation to the 
upcoming instructions:
* To perform the fast install on Debian and Debian-derived Linux 
distributions simply run `debian-fast-install.sh`
* For installing on a generic Linux distribution start by ensuring that git, curl, python3 and python3-pip are available, run `linux-lean-install.sh` and set up VS Code (or Emacs)
* For installing on Windows install Git for Windows, run `windows-lean-install-1.sh`, install python3, run `windows-lean-install-2.sh` and set up VS Code (or Emacs)
* For cloning the project from github run `clone-project.sh` in the desired folder


Installing Lean
===============

These instructions have been synthesised from the official 
[Lean website](https://leanprover-community.github.io/get_started.html)

Script files for everything are included in the zip file.

*Note: Lean can only be used with a supported code editor of which there 
are currently only two: Visual Studio Code and Emacs*

Debian and Debian-derived Linux distributions:
----------------------------------------------
Official Instructions: https://leanprover-community.github.io/install/debian.html

The quickest way to install everything required to run Lean is by running 
the following command in a terminal:

```
wget -q https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile
```

This installs Lean along with elan, the Lean version manager, leanpkg, 
Lean's package manager, leanproject, the supporting tool for mathlib 
projects, Microsoft's Visual Studio Code https://code.visualstudio.com/ 
and dependency tools git, curl, python3, python3-pip, pipx and 
python3-venv. For a more controlled approach follow the instructions at 
https://leanprover-community.github.io/install/debian_details.html

Generic Linux distribution:
---------------------------
Official instructions: https://leanprover-community.github.io/install/linux.html

First install git, curl, python3 and python3-pip.
Then install elan, the Lean version manager, using the command:

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Now install either [Visual Studio Code](https://code.visualstudio.com/) 
or [Emacs](https://www.gnu.org/software/emacs/download.html). Using VS 
Code is strongly recommended.

To set up VSCode:
  * Install [VS Code](https://code.visualstudio.com/)
  * Open VS Code
  * Open the extension menu from the left sidebar icon or by pressing
  `Ctrl-Shift-X`
  * Type `leanprover` in the searchbar then select and install the
  `lean` extension. (there will also be the `lean4` extension, 
  however, this does not 
    work with mathlib)
  * You can verify that Lean is working by creating a file called 
  `test.lean` and typing `#eval 1 + 1`. `eval` should be underlined
  and hovering the mouse over it should display `2`. There should also
  be a "Lean Infoview" area on the right side of VS Code and placing 
  the cursor at the end of the line should display `2` in the "Lean Infoview" area.

To set up Emacs follow the instructions at 
https://github.com/leanprover/lean-mode

Finally, to install the tools required for mathlib, run the commands:

```
python3 -m pip install --user pipx
python3 -m pipx ensurepath
source ~/.profile
pipx install mathlibtools
```

Windows
-------
Official instructions: https://leanprover-community.github.io/install/windows.html

First, a terminal is required. The recommended terminal is 
[Git for Windows](https://gitforwindows.org/).

Configure git by running the following command in the terminal:

```
git config --global core.autocrlf input
```

Next, run the following command in the terminal to install elan, the Lean version manager:

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Now add the installed files to the PATH by running the command below and 
restart the terminal:

```
'PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.profile"
```

Now install [python3](https://www.python.org/downloads/) and make sure it 
is added to the PATH. Then set up the `python3` command by running:

```
cp "$(which python)" "$(which python)"3
```

Check that everything is installed correctly by running the commands:

```
python3 --version
pip3 --version
```

If `pip3 --version` gives no output run the command:

```
python3 -m pip install --upgrade pip
```

Now install the tools required for mathlib by running:

```
pip3 install mathlibtools
```

Finally set up VS Code(or Emacs) as shown for the generic linux 
distribution above.



Compiling the project
=====================

The project is included in the zip file but to clone the project from github run:

```
leanproject get https://github.com/1034461/4th_year_project.git
```

The `src` folder in the project folder contains the `.lean` files which 
hold our proofs and definitions.

If using VS Code open the project in the editor either manually or by 
running `code 4th_year_project` in the terminal. Opening any of the 
`.lean` files should open the "Lean Infoview" area on the right side of 
the editor. If "Lean Infoview" is not there, then pressing 
`Ctrl-Shift-Enter` should open it. To check any of the proofs move the 
cursor inside the tactic block and the "Lean Infoview" panel should 
display the tactic state. Placing the cursor after the last tactic (after 
the last comma) should display "goals accomplished", ensuring that that 
the proof has achieved its goal. The project is compiled automatically 
and the successful compilation indicates that all proofs and definitions 
are correct.

If using Emacs follow the instructions at https://github.com/leanprover/lean-mode