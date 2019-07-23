use crate::syntax;
use super::*;

type Result = crate::syntax::display::Result;

impl syntax::Display for Model {
    fn fmt(&self, f: &mut syntax::Formatter) -> Result {
        f.tabulated_list(&self.definitions)
    }
}

impl syntax::Display for Definition {
    fn fmt(&self, f: &mut syntax::Formatter) -> Result {
        f.comments(&self.comments);
        f.begin()?;

        if self.rec {
            if self.declarations.len() == 1 {
                f.keyword("define-fun-rec")?;
                let decl = &self.declarations[0];

                f.symbol(&decl.id)?;
                f.list(&decl.args)?;
                decl.return_sort.fmt(f)?;

                let body = &self.bodies[0];
                body.fmt(f)?;
            } else {
                f.keyword("define-funs-rec")?;

                f.tabulated_list(&self.declarations)?;
                f.tabulated_list(&self.bodies)?;
            }
        } else {
            f.keyword("define-fun")?;

            let decl = &self.declarations[0];

            f.symbol(&decl.id)?;
            f.list(&decl.args)?;
            decl.return_sort.fmt(f)?;

            let body = &self.bodies[0];
            body.fmt(f)?;
        }

        f.end()
    }
}

impl syntax::Display for Declaration {
    fn fmt(&self, f: &mut syntax::Formatter) -> Result {
        f.begin()?;
        f.symbol(&self.id)?;
        f.list(&self.args)?;
        self.return_sort.fmt(f)?;
        f.end()
    }
}
