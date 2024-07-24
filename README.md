# Template for Coq-Projects on Github

This is a template for Github Coq-Projects.

## Usage

You can use this template by clicking on the "Use this template"-Button:
![grafik](https://github.com/motrellin/comoproj/assets/105235679/450ab9bf-22ff-4961-9091-4959c8643471)

Choose to "Create a new repository". You should choose to create a public repository in order to deploy to Github Pages which is a main advantage of this project. 
Make sure to enable Github Pages for your project. (Source: Github Actions)

After that, clone your new repository and update the `meta.yml`. 
You should ahve a look at the [`ref.yml`](https://github.com/coq-community/templates/blob/master/ref.yml) from Coq-Community.

You must also update the following line in the `Makefile`:
```
COMPONENTS := theories:CoMoProj
```
It should match your choosen namespace.

Now execute
```
./generate.sh
git add .
git commit
git push
```
To generate meta information about your project.

## Licensing

Do not hesitate to use this template.
Please note, that the [Makefile](Makefile) is licensed under GNU General Public License v3.0.
It was first published at [Gitlab](https://gitlab.cs.fau.de/oc59yqul/template-coq/-/blob/main/Makefile?ref_type=heads)
