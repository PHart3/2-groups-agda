## Manual Type-Checking

1. Install Agda 2.6.4.3.
2. Add the lib files in the four sub-directories of `../` to your Agda libraries file. 
3. Type-check the file `Final-thms.agda`.

The type-checking of this file is very intensive. We have verfied that the type-checker
finishes successfully on the following machine:

*macOS Sequoia 15.4.1, Apple M1 chip, 16 GB of RAM*

The type-checking takes just under 165 minutes in total (see [stats.md](stats.md)).
Note that macOS, unlike Linux, dynamically alters the size of the swap
space as the process runs. This is crucial because the type-checking uses
as much as 29 GB of physical memory. Therefore, you will need to increase
your machine's swap space if you have under 29 GB of available RAM.

## License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt)