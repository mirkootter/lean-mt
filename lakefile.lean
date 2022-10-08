import Lake
open Lake DSL

package mt {
  -- add package configuration options here
}

@[defaultTarget]
lean_lib Mt {
  -- add library configuration options here
}

lean_lib Samples {
  
}

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
