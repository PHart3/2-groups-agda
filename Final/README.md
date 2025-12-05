## Manual Type-Checking

1. Install Agda 2.6.4.3.
2. Add all lib files in the repo to your Agda libraries file. 
3. Type-check the file `Final-thms.agda`.

The type-checking of this file is arduous. We have verified that the type-checker
finishes successfully on the following machine:

*macOS Sequoia 15.4.1, Apple M1 chip, 16 GB of RAM*

The type-checking takes about 255 minutes in total (see [stats.md](stats.md)).
Note that macOS, unlike Linux, dynamically alters the size of the swap
space as the process runs. This is crucial because the type-checking uses
as much as 28 GB of physical memory. Therefore, you will need to increase
your machine's swap space if you have under 28 GB of available RAM.

**Important:** Comment out the final three imports in `Final-thms` to reduce the amount of type-checking by over half.
Doing so will check all relevant type equivalences but not the biequivalence (which takes up most of the total time).

**Note:** We have included all of the `.agdai` files (in the various `_build` directories) in case you do
not want to perform the intensive type-checking on your machine from scratch. Pass the flag `--ignore-interfaces`
to `agda` if you want to type check `Final-thms.agda` from scratch.

## License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt).
