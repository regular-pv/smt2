use crate::syntax;
use super::*;

type Result = crate::syntax::display::Result;

impl<F: Clone> syntax::Display for Model<F> {
    fn fmt(&self, f: &mut syntax::Formatter) -> Result {
        f.list(&self.definitions)
    }
}

impl<F: Clone> syntax::Display for Definition<F> {
    fn fmt(&self, f: &mut syntax::Formatter) -> Result {
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

impl<F: Clone> syntax::Display for Declaration<F> {
    fn fmt(&self, f: &mut syntax::Formatter) -> Result {
        f.begin()?;
        f.symbol(&self.id)?;
        f.list(&self.args)?;
        self.return_sort.fmt(f)?;
        f.end()
    }
}
