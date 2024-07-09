
/**
 * ➀ Categories, allowing products to be classified in categories
 * ➁ Hierarchical categories, allowing hierarchical categories;
 * ➂ Multiple categories, allowing a product to belong to multiple categories
*/
fact FeatureModel {
    ➁➊some none➊➁ -- Hierarchical requires Categories
    ➂➊some none➊➂ -- Multiple requires Categories
}
sig Product {
    ➊ catalog : one Catalog ➊,
    ➀➌ category : one Category ➌➀, 
    ➀➂ category : some Category ➂➀, 
    images : set Image
    }
sig Image {}
sig Catalog {thumbnails : set Image }
➀➁sig Category { inside : one Catalog + Category }➁➀
➀➋ sig Category {inside : one Catalog } ➋➀

➀➁fact Acyclic {
    all c : Category | c not in c.^inside
}➁➀

fact Thumbnails{
    ➊all c : Catalog | c.thumbnails in catalog.c.images➊
    ➀ all c : Catalog | c.thumbnails in (category.(➋inside ➋ + ➁^inside ➁).c).images ➀
}

➀➁assert AllCataloged {
 all p: Product | some (p.category.^inside & Catalog)
}➁➀
check  AllCataloged with exactly ➀,➁
