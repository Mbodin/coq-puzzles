A collection of puzzles formalised in Coq.

The project is organised as follows:
- [lib/](lib/) contains some generic useful files.
- [tiles.v](theories/tiles.v) is about a two-player game with tiles to be removed at each step.

# Installation

An `esy` packaging is provided.
The following lines will fetch and install all dependencies, as well as compiling the project.
```bash
sudo apt install npm git curl m4 autoconf
sudo npm install --global esy@latest # Tested with version 0.6.6 of esy.
esy
```

# License
© Intellectual property right of Martin Bodin, 2020.
This program is released under the CeCILL-C license.
See [LICENSE](LICENSE) for more information.

